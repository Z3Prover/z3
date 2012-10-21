/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    user_simplifier_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-22.

Revision History:

--*/
#include"user_simplifier_plugin.h"
#include"ast_pp.h"
#include"warning.h"

user_simplifier_plugin::user_simplifier_plugin(symbol const & fname, ast_manager & m):
    simplifier_plugin(fname, m),
    m_owner(0),
    m_enabled(true),
    m_reduce_app_fptr(0),
    m_reduce_eq_fptr(0),
    m_reduce_distinct_fptr(0) {
}

simplifier_plugin * user_simplifier_plugin::mk_fresh() {
    ast_manager & m = get_manager();
    user_simplifier_plugin * new_sp = alloc(user_simplifier_plugin, m.get_family_name(get_family_id()), m);
    new_sp->m_reduce_app_fptr      = m_reduce_app_fptr;
    new_sp->m_reduce_eq_fptr       = m_reduce_eq_fptr;
    new_sp->m_reduce_distinct_fptr = m_reduce_distinct_fptr;
    return new_sp;
}

bool user_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (m_reduce_app_fptr == 0 || !m_enabled)
        return false;
    expr * _result = 0;
    bool flag = m_reduce_app_fptr(m_owner, f, num_args, args, &_result);
    if (flag) {
        if (_result == 0)
            throw default_exception("invalid reduce_app callback: result is null");
        result = _result;
    } 
    return flag;
}

bool user_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    if (m_reduce_eq_fptr == 0 || !m_enabled)
        return false;
    expr * _result = 0;
    bool flag = m_reduce_eq_fptr(m_owner, lhs, rhs, &_result);
    if (flag) {
        if (_result == 0)
            throw default_exception("invalid reduce_eq callback: result is null");
        result = _result;
    }
    return flag;
}

bool user_simplifier_plugin::reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result) {
    if (m_reduce_distinct_fptr == 0 || !m_enabled)
        return false;
    expr * _result = 0;
    bool flag = m_reduce_distinct_fptr(m_owner, num_args, args, &_result);
    if (flag) {
        if (_result == 0)
            throw default_exception("invalid reduce_distinct callback: result is null");
        result = _result;
    }
    return flag;
}

void user_simplifier_plugin::flush_caches() {
}
