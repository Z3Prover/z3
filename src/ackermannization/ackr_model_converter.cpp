/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ackr_model_converter.cpp

Abstract:

Author:

    Mikolas Janota

Revision History:
--*/
#include "ackermannization/ackr_model_converter.h"
#include "model/model_evaluator.h"
#include "ast/ast_smt2_pp.h"
#include "ackermannization/ackr_info.h"


class ackr_model_converter : public model_converter {
public:
    ackr_model_converter(ast_manager & m,
                         const ackr_info_ref& info,
                         model_ref& abstr_model)
        : m(m)
        , info(info)
        , abstr_model(abstr_model)
        , fixed_model(true)
    { }

    ackr_model_converter(ast_manager & m,
                         const ackr_info_ref& info)
        : m(m)
        , info(info)
        , fixed_model(false)
    { }

    ~ackr_model_converter() override { }

    void get_units(obj_map<expr, bool>& units) override { units.reset(); }

    void operator()(model_ref & md) override {
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
        out << "(ackr-model-converter)\n";
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
    void convert_constants(model * source, model * destination);
};

void ackr_model_converter::convert(model * source, model * destination) {
    destination->copy_func_interps(*source);
    destination->copy_usort_interps(*source);
    convert_constants(source, destination);
}

void ackr_model_converter::convert_constants(model * source, model * destination) {
    TRACE("ackr_model", tout << "converting constants\n";);
    obj_map<func_decl, func_interp*> interpretations;
    model_evaluator evaluator(*source);
    evaluator.set_model_completion(true);
    for (unsigned i = 0; i < source->get_num_constants(); i++) {
        func_decl * const c = source->get_constant(i);
        app * const term = info->find_term(c);
        expr * value = source->get_const_interp(c);
        if (!term) {
            destination->register_decl(c, value);
        }
        else {
            add_entry(evaluator, term, value, interpretations);
        }
    }

    obj_map<func_decl, func_interp*>::iterator e = interpretations.end();
    for (obj_map<func_decl, func_interp*>::iterator i = interpretations.begin();
         i != e; ++i) {
        func_decl* const fd = i->m_key;
        func_interp* const fi = i->get_value();
        fi->set_else(m.get_some_value(fd->get_range()));
        destination->register_decl(fd, fi);
    }
}

void ackr_model_converter::add_entry(model_evaluator & evaluator,
                                     app* term, expr* value,
                                     obj_map<func_decl, func_interp*>& interpretations) {
    TRACE("ackr_model", tout << "add_entry"
          << mk_ismt2_pp(term, m, 2)
          << "->"
          << mk_ismt2_pp(value, m, 2) << "\n";
    );

    func_interp * fi = nullptr;
    func_decl * const declaration = term->get_decl();
    const unsigned sz = declaration->get_arity();
    SASSERT(sz == term->get_num_args());
    if (!interpretations.find(declaration, fi)) {
        fi = alloc(func_interp, m, sz);
        interpretations.insert(declaration, fi);
    }
    expr_ref_vector args(m);
    for (unsigned gi = 0; gi < sz; ++gi) {
        expr * const arg = term->get_arg(gi);
        expr_ref aarg(m);
        info->abstract(arg, aarg);
        expr_ref arg_value(m);
        evaluator(aarg, arg_value);
        args.push_back(arg_value);
    }
    if (fi->get_entry(args.c_ptr()) == nullptr) {
        TRACE("ackr_model",
              tout << mk_ismt2_pp(declaration, m) << " args: " << std::endl;
                for (unsigned i = 0; i < args.size(); i++)
                    tout << mk_ismt2_pp(args.get(i), m) << std::endl;
                tout << " -> " << mk_ismt2_pp(value, m) << "\n"; );
        fi->insert_new_entry(args.c_ptr(), value);
    }
    else {
        TRACE("ackr_model", tout << "entry already present\n";);
    }

}

model_converter * mk_ackr_model_converter(ast_manager & m, const ackr_info_ref& info) {
    return alloc(ackr_model_converter, m, info);
}

model_converter * mk_ackr_model_converter(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model) {
    return alloc(ackr_model_converter, m, info, abstr_model);
}
