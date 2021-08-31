/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_converter.h

Abstract:

    Abstract interface for converting models.

Author:

    Leonardo (leonardo) 2011-04-21

Notes:

--*/
#include "tactic/model_converter.h"
#include "model/model_v2_pp.h"
#include "ast/ast_smt2_pp.h"

/*
 * Add or overwrite value in model.
 */
void model_converter::display_add(std::ostream& out, ast_manager& m, func_decl* f, expr* e) const {
    VERIFY(e);
    smt2_pp_environment_dbg env(m);
    smt2_pp_environment* _env = m_env ? m_env : &env;
    VERIFY(f->get_range() == e->get_sort());
    ast_smt2_pp(out, f, e, *_env, params_ref(), 0, "model-add") << "\n";
}

/*
 * A value is removed from the model.
 */
void model_converter::display_del(std::ostream& out, func_decl* f) const {
    if (m_env) {
        ast_smt2_pp(out << "(model-del ", f->get_name(), f->is_skolem(), *m_env) << ")\n";    
    }
    else {
        out << "(model-del " << f->get_name() << ")\n";
    }
}

void model_converter::set_env(ast_pp_util* visitor) {
    if (visitor) {
        m_env = &visitor->env();
    }
    else {
        m_env = nullptr;
    }
}


void model_converter::display_add(std::ostream& out, ast_manager& m) {
    // default printer for converter that adds entries
    model_ref mdl = alloc(model, m);
    (*this)(mdl);
    for (unsigned i = 0, sz = mdl->get_num_constants(); i < sz; ++i) {
        func_decl* f = mdl->get_constant(i);
        display_add(out, m, f, mdl->get_const_interp(f));
    }
    for (unsigned i = 0, sz = mdl->get_num_functions(); i < sz; ++i) {
        func_decl* f = mdl->get_function(i);
        func_interp* fi = mdl->get_func_interp(f);
        display_add(out, m, f, fi->get_interp());
    }
}


class concat_model_converter : public concat_converter<model_converter> {
public:
    concat_model_converter(model_converter * mc1, model_converter * mc2): concat_converter<model_converter>(mc1, mc2) {
        VERIFY(m_c1 && m_c2);
    }

    void operator()(model_ref & m) override {
        this->m_c2->operator()(m);
        this->m_c1->operator()(m);
    }

    void operator()(expr_ref & fml) override {
        this->m_c2->operator()(fml);
        this->m_c1->operator()(fml);
    }
    
    void operator()(labels_vec & r) override {
        this->m_c2->operator()(r);
        this->m_c1->operator()(r);
    }

    void get_units(obj_map<expr, bool>& fmls) override {
        m_c2->get_units(fmls);
        m_c1->get_units(fmls);
    }
  
    char const * get_name() const override { return "concat-model-converter"; }

    model_converter * translate(ast_translation & translator) override {
        return this->translate_core<concat_model_converter>(translator);
    }

    void set_env(ast_pp_util* visitor) override {
        this->m_c1->set_env(visitor);
        this->m_c2->set_env(visitor);
    }
};

model_converter * concat(model_converter * mc1, model_converter * mc2) {
    if (mc1 == nullptr)
        return mc2;
    if (mc2 == nullptr)
        return mc1;
    return alloc(concat_model_converter, mc1, mc2);
}


class model2mc : public model_converter {
    model_ref m_model;
    labels_vec m_labels;
public:
    model2mc(model * m):m_model(m) {}

    model2mc(model * m, labels_vec const & r):m_model(m), m_labels(r) {}

    ~model2mc() override {}

    void operator()(model_ref & m) override {
        if (!m || !m_model) {
            m = m_model;
            return;
        }
        m->copy_const_interps(*m_model.get());
        m->copy_func_interps(*m_model.get());
        m->copy_usort_interps(*m_model.get());
    }

    void operator()(labels_vec & r) override {
        r.append(m_labels.size(), m_labels.data());
    }

    void operator()(expr_ref& fml) override {
        model::scoped_model_completion _scm(m_model, false);
        fml = (*m_model)(fml);
    }

    void get_units(obj_map<expr, bool>& fmls) override {
        // no-op
    }

    void cancel() override {
    }
    
    void display(std::ostream & out) override {
        out << "(rmodel->model-converter-wrapper\n";
        model_v2_pp(out, *m_model);
        out << ")\n";
    }    
    
    model_converter * translate(ast_translation & translator) override {
        model * m = m_model->translate(translator);
        return alloc(model2mc, m, m_labels);
    }

};

model_converter * model2model_converter(model * m) {
    if (!m) return nullptr;
    return alloc(model2mc, m);
}

model_converter * model_and_labels2model_converter(model * m, labels_vec const & r) {
    if (!m) return nullptr;
    return alloc(model2mc, m, r);
}

void model_converter2model(ast_manager & mng, model_converter * mc, model_ref & m) {
    if (mc) {
        m = alloc(model, mng);
        (*mc)(m);
    }
}

void apply(model_converter_ref & mc, model_ref & m) {
    if (mc) {
        (*mc)(m);
    }
}

