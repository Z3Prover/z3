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
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "model/model_evaluator.h"
#include "model/model_v2_pp.h"
#include "tactic/extension_model_converter.h"

extension_model_converter::~extension_model_converter() {
}

#ifdef _TRACE
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
#endif

void extension_model_converter::operator()(model_ref & md, unsigned goal_idx) {
    SASSERT(goal_idx == 0);
    TRACE("extension_mc", model_v2_pp(tout, *md); display_decls_info(tout, md););
    model_evaluator ev(*(md.get()));
    ev.set_model_completion(true);
    ev.set_expand_array_equalities(false);
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
            new_fi->set_else(val);
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
    for (unsigned i = 0; i < m_vars.size(); i++) {
        display_add(out, m(), m_vars.get(i), m_defs.get(i));
    }
}

model_converter * extension_model_converter::translate(ast_translation & translator) {
    extension_model_converter * res = alloc(extension_model_converter, translator.to());
    for (func_decl* v : m_vars)
        res->m_vars.push_back(translator(v));
    for (expr* d : m_defs) 
        res->m_defs.push_back(translator(d));
    return res;
}

