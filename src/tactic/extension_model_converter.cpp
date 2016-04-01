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

bool extension_model_converter::is_fi_entry_expr(expr * e, unsigned arity, ptr_vector<expr> & args) {
    args.reset();
    if (!is_app(e) || !m().is_ite(to_app(e)))
        return false;

    app * a = to_app(e);
    expr * c = a->get_arg(0);
    expr * t = a->get_arg(1);
    expr * f = a->get_arg(2);

    if ((arity == 0) ||
        (arity == 1 && (!m().is_eq(c) || to_app(c)->get_num_args() != 2)) ||
        (arity > 1 && (!m().is_and(c) || to_app(c)->get_num_args() != arity)))
        return false;

    args.resize(arity, 0);
    for (unsigned i = 0; i < arity; i++) {
        expr * ci = (arity == 1 && i == 0) ? to_app(c) : to_app(c)->get_arg(i);

        if (!m().is_eq(ci) || to_app(ci)->get_num_args() != 2)
            return false;

        expr * a0 = to_app(ci)->get_arg(0);
        expr * a1 = to_app(ci)->get_arg(1);
        if (is_var(a0) && to_var(a0)->get_idx() == i)
            args[i] = a1;
        else if (is_var(a1) && to_var(a1)->get_idx() == i)
            args[i] = a0;
        else
            return false;
    }

    return true;
}

void extension_model_converter::operator()(model_ref & md, unsigned goal_idx) {
    SASSERT(goal_idx == 0);
    TRACE("extension_mc", model_v2_pp(tout, *md); display_decls_info(tout, md););
    model_evaluator ev(*(md.get()));
    ev.set_model_completion(true);
    expr_ref val(m());
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
            expr * e = val.get();
            ptr_vector<expr> args;
            while (is_fi_entry_expr(e, arity, args)) {
                TRACE("extension_mc", tout << "fi entry: " << mk_ismt2_pp(e, m()) << std::endl;);
                new_fi->insert_entry(args.c_ptr(), to_app(e)->get_arg(1));
                e = to_app(e)->get_arg(2);
            }
            new_fi->set_else(e);
            md->register_decl(f, new_fi);
        }
    }
    TRACE("extension_mc", model_v2_pp(tout, *md); display_decls_info(tout, md););
}

void extension_model_converter::insert(func_decl * v, expr * def) {
    m_vars.push_back(v);
    m_defs.push_back(def);
}


void extension_model_converter::display(std::ostream & out) {
    out << "(extension-model-converter";
    for (unsigned i = 0; i < m_vars.size(); i++) {
        out << "\n  (" << m_vars.get(i)->get_name() << " ";
        unsigned indent = m_vars.get(i)->get_name().size() + 4;
        out << mk_ismt2_pp(m_defs.get(i), m(), indent) << ")";
    }
    out << ")" << std::endl;
}

model_converter * extension_model_converter::translate(ast_translation & translator) {
    extension_model_converter * res = alloc(extension_model_converter, translator.to());
    for (unsigned i = 0; i < m_vars.size(); i++)
        res->m_vars.push_back(translator(m_vars[i].get()));
    for (unsigned i = 0; i < m_defs.size(); i++)
        res->m_defs.push_back(translator(m_defs[i].get()));
    return res;
}
