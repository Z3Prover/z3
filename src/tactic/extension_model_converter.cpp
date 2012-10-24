/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    extension_model_converter.cpp

Abstract:

    Model converter that introduces eliminated variables in a model.

Author:

    Leonardo (leonardo) 2011-10-21

Notes:

--*/
#include"extension_model_converter.h"
#include"model_evaluator.h"
#include"ast_smt2_pp.h"
#include"model_v2_pp.h"
#include"ast_pp.h"

extension_model_converter::~extension_model_converter() {
}

struct extension_model_converter::set_eval {
    extension_model_converter * m_owner;
    model_evaluator *          m_old;
    set_eval(extension_model_converter * owner, model_evaluator * ev) {
        m_owner = owner;
        m_old   = owner->m_eval;
        #pragma omp critical (extension_model_converter) 
        {
            owner->m_eval = ev;
        }
    }
    ~set_eval() {
        #pragma omp critical (extension_model_converter)
        {
            m_owner->m_eval = m_old;
        }
    }
    
};

static void display_decls_info(std::ostream & out, model_ref & md) {
    ast_manager & m = md->get_manager();
    unsigned sz = md->get_num_decls();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * d = md->get_decl(i);
        out << d->get_name();
        out << " (";
        for (unsigned j = 0; j < d->get_arity(); j++)
            out << mk_pp(d->get_domain(j), m);
        out << mk_pp(d->get_range(), m);
        out << ") ";
        if (d->get_info())
            out << *(d->get_info());
        out << " :id " << d->get_id() << "\n";
    }
}

void extension_model_converter::operator()(model_ref & md, unsigned goal_idx) {
    SASSERT(goal_idx == 0);
    TRACE("extension_mc", model_v2_pp(tout, *md); display_decls_info(tout, md););
    model_evaluator ev(*(md.get()));
    ev.set_model_completion(true);
    expr_ref val(m());
    {
        set_eval setter(this, &ev);
        unsigned i = m_vars.size();
        while (i > 0) {
            --i;
            expr * def = m_defs.get(i);
            ev(def, val);
            TRACE("extension_mc", tout << m_vars.get(i)->get_name() << " ->\n" << mk_ismt2_pp(def, m()) << "\n==>\n" << mk_ismt2_pp(val, m()) << "\n";);
            func_decl * f  = m_vars.get(i);
            unsigned arity = f->get_arity();
            if (arity == 0) {
                md->register_decl(f, val);
            }
            else {
                func_interp * new_fi = alloc(func_interp, m(), arity);
                new_fi->set_else(val);
                md->register_decl(f, new_fi);
            }
        }
    }
    TRACE("extension_mc", model_v2_pp(tout, *md); display_decls_info(tout, md););
}

void extension_model_converter::cancel() {
    #pragma omp critical (extension_model_converter) 
    {
        if (m_eval)
            m_eval->cancel();
    }
}

void extension_model_converter::display(std::ostream & out) {
    ast_manager & m = m_vars.get_manager();
    out << "(extension-model-converter";
    for (unsigned i = 0; i < m_vars.size(); i++) {
        out << "\n  (" << m_vars.get(i)->get_name() << " ";
        unsigned indent = m_vars.get(i)->get_name().size() + 4;
        out << mk_ismt2_pp(m_defs.get(i), m, indent) << ")";
    }
    out << ")" << std::endl;
}

model_converter * extension_model_converter::translate(ast_translation & translator) {
    extension_model_converter * res = alloc(extension_model_converter, translator.to());    
    for (unsigned i = 0; i < m_vars.size(); i++)
        res->m_vars.push_back(translator(m_vars[i].get()));
    for (unsigned i = 0; i < m_defs.size(); i++)
        res->m_defs.push_back(translator(m_defs[i].get()));    
    // m_eval is a transient object. So, it doesn't need to be translated.
    return res;
}
