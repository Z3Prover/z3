/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ackr_model_converter.cpp

Abstract:

Author:

    Mikolas Janota

Revision History:
--*/

#include "ast/ast_smt2_pp.h"
#include "ast/array_decl_plugin.h"
#include "model/model_evaluator.h"
#include "ackermannization/ackr_model_converter.h"
#include "ackermannization/ackr_info.h"


class ackr_model_converter : public model_converter {
public:
    ackr_model_converter(ast_manager & m,
                         const ackr_info_ref& info,
                         model_ref& abstr_model)
        : m(m),
          info(info),
          abstr_model(abstr_model),
          fixed_model(true)
    { 
    }

    ackr_model_converter(ast_manager & m,
                         const ackr_info_ref& info)
        : m(m),
          info(info),
          fixed_model(false)
    { }

    ~ackr_model_converter() override { }

    void get_units(obj_map<expr, bool>& units) override { units.reset(); }

    void operator()(model_ref & md) override {
        TRACE("ackermannize", tout << (fixed_model? "fixed" : "nonfixed") << "\n";);
        SASSERT(!fixed_model || md.get() == 0 || (!md->get_num_constants() && !md->get_num_functions()));
        model_ref& old_model = fixed_model ? abstr_model : md;
        SASSERT(old_model.get());
        model * new_model = alloc(model, m);
        convert(old_model.get(), new_model);
        md = new_model;
    }

    model_converter * translate(ast_translation & translator) override {
        ackr_info_ref retv_info = info->translate(translator);
        if (fixed_model) {
            model_ref retv_mod_ref = abstr_model->translate(translator);
            return alloc(ackr_model_converter, translator.to(), retv_info, retv_mod_ref);
        }
        else {
            return alloc(ackr_model_converter, translator.to(), retv_info);
        }
    }

    void display(std::ostream & out) override {
        out << "(ackr-model-converter";
        if (abstr_model)
            out << *abstr_model;
        out << ")\n";
    }

protected:
    ast_manager &             m;
    const ackr_info_ref       info;
    model_ref                 abstr_model;
    bool                      fixed_model;
    void convert(model * source, model * destination);
    void add_entry(model_evaluator & evaluator,
                   app* term, expr* value,
                   obj_map<func_decl, func_interp*>& interpretations);
    void add_entry(model_evaluator & evaluator,
                   app* term, expr* value,
                   obj_map<app, expr*>& interpretations);
    void convert_constants(model * source, model * destination);
};

void ackr_model_converter::convert(model * source, model * destination) {
    destination->copy_func_interps(*source);
    destination->copy_usort_interps(*source);
    convert_constants(source, destination);
}

void ackr_model_converter::convert_constants(model * source, model * destination) {
    TRACE("ackermannize", tout << "converting constants\n";);
    obj_map<func_decl, func_interp*> interpretations;
    obj_map<app, expr*> array_interpretations; 
    model_evaluator evaluator(*source);
    evaluator.set_model_completion(true);
    array_util autil(m);

    for (unsigned i = 0; i < source->get_num_constants(); i++) {
        func_decl * const c = source->get_constant(i);
        app * const term = info->find_term(c);
        expr * value = source->get_const_interp(c);
        TRACE("ackermannize", tout << mk_ismt2_pp(c, m) << " " << mk_ismt2_pp(term, m) << "\n";);
        if (!term) 
            destination->register_decl(c, value);
        else if (autil.is_select(term)) 
            add_entry(evaluator, term, value, array_interpretations);
        else 
            add_entry(evaluator, term, value, interpretations);
    }

    for (auto & kv : interpretations) {
        func_decl* const fd = kv.m_key;
        func_interp* const fi = kv.m_value;
        fi->set_else(m.get_some_value(fd->get_range()));
        destination->register_decl(fd, fi);
    }
    for (auto & kv : array_interpretations) {
        destination->register_decl(kv.m_key->get_decl(), kv.m_value);
    }
}

void ackr_model_converter::add_entry(model_evaluator & evaluator,
                                     app* term, expr* value,
                                     obj_map<app, expr*>& array_interpretations) {
    
    array_util autil(m);
    app* A = to_app(term->get_arg(0));
    expr * e = nullptr, *c = nullptr;
    if (!array_interpretations.find(A, e)) {
        e = autil.mk_const_array(A->get_sort(), value);
    }
    else {
        // avoid storing the same as the default value.
        c = e;
        while (autil.is_store(c)) c = to_app(c)->get_arg(0);
        if (autil.is_const(c, c) && c == value) {
            return;
        }
        expr_ref_vector args(m);
        unsigned sz = term->get_num_args();
        args.push_back(e);
        for (unsigned i = 1; i < sz; ++i) {
            expr * arg = term->get_arg(i);
            args.push_back(evaluator(info->abstract(arg)));
        }    
        args.push_back(value);
        e = autil.mk_store(args.size(), args.data());
    }
    array_interpretations.insert(A, e);
}

void ackr_model_converter::add_entry(model_evaluator & evaluator,
                                     app* term, expr* value,
                                     obj_map<func_decl, func_interp*>& interpretations) {
    TRACE("ackermannize", tout << "add_entry"
          << mk_ismt2_pp(term, m, 2)
          << "->"
          << mk_ismt2_pp(value, m, 2) << "\n";);

    func_interp * fi = nullptr;
    func_decl * const declaration = term->get_decl();
    const unsigned sz = declaration->get_arity();
    SASSERT(sz == term->get_num_args());
    if (!interpretations.find(declaration, fi)) {
        fi = alloc(func_interp, m, sz);
        interpretations.insert(declaration, fi);
    }
    expr_ref_vector args(m);
    for (expr* arg : *term) {
        args.push_back(evaluator(info->abstract(arg)));
    }
    if (fi->get_entry(args.data()) == nullptr) {
        TRACE("ackermannize",
              tout << mk_ismt2_pp(declaration, m) << " args: " << std::endl;
              for (expr* arg : args) {
                  tout << mk_ismt2_pp(arg, m) << std::endl;
              }
              tout << " -> " << mk_ismt2_pp(value, m) << "\n"; );
        fi->insert_new_entry(args.data(), value);
    }
    else {
        TRACE("ackermannize", tout << "entry already present\n";);
    }

}

model_converter * mk_ackr_model_converter(ast_manager & m, const ackr_info_ref& info) {
    return alloc(ackr_model_converter, m, info);
}

model_converter * mk_ackr_model_converter(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model) {
    return alloc(ackr_model_converter, m, info, abstr_model);
}
