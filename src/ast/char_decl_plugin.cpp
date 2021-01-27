/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    char_decl_plugin.cpp

Abstract:

    char_plugin for unicode suppport

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-26


--*/
#pragma once

#include "util/zstring.h"
#include "ast/char_decl_plugin.h"

char_decl_plugin::char_decl_plugin() : m_charc_sym("Char") {
}

func_decl* char_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                        unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    switch (k) {
    case OP_CHAR_LE:
        if (arity == 2 && domain[0] == m_char && domain[1] == m_char) 
            return m.mk_func_decl(symbol("char.<="), arity, domain, m.mk_bool_sort(), func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception("Incorrect parameters passed to character comparison");
    case OP_CHAR_CONST:
        if (num_parameters == 1 && 
            arity == 0 && 
            parameters[0].is_int() && 
            0 <= parameters[0].get_int() && 
            parameters[0].get_int() < static_cast<int>(zstring::unicode_max_char()))
            return m.mk_const_decl(m_charc_sym, m_char, func_decl_info(m_family_id, OP_CHAR_CONST, num_parameters, parameters));
        m.raise_exception("invalid character declaration");
    default:
        UNREACHABLE();
    }    
    return nullptr;
}

void char_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_char = m->mk_sort(symbol("Unicode"), sort_info(m_family_id, CHAR_SORT, 0, nullptr));
    m->inc_ref(m_char);
}

void char_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const& logic) {
    op_names.push_back(builtin_name("char.<=", OP_CHAR_LE));
}

void char_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) {
    sort_names.push_back(builtin_name("Unicode",  CHAR_SORT));
}

bool char_decl_plugin::is_value(app* e) const {
    return is_app_of(e, m_family_id, OP_CHAR_CONST);
}

bool char_decl_plugin::is_unique_value(app* e) const {
    return is_value(e);
}

bool char_decl_plugin::are_equal(app* a, app* b) const {
    return a == b;
}

bool char_decl_plugin::are_distinct(app* a, app* b) const {
    return 
        a != b && 
        is_app_of(a, m_family_id, OP_CHAR_CONST) && 
        is_app_of(b, m_family_id, OP_CHAR_CONST); 
}

app* char_decl_plugin::mk_char(unsigned u) {
    parameter param(u);
    func_decl* f = m_manager->mk_const_decl(m_charc_sym, m_char, func_decl_info(m_family_id, OP_CHAR_CONST, 1, &param));
    return m_manager->mk_const(f);
}

expr* char_decl_plugin::get_some_value(sort* s) {
    return mk_char(0);
}
