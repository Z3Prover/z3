/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    order.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-15.

Revision History:

--*/

#include"order.h"

bool order::equal(expr_offset const & _t1, expr_offset const & _t2, substitution * s) {
    if (_t1 == _t2)
        return true;
    if (s == 0)
        return false;
    m_eq_todo.reset();
    m_eq_todo.push_back(expr_offset_pair(_t1, _t2));
    while (!m_eq_todo.empty()) {
        expr_offset_pair const & p = m_eq_todo.back();
        expr_offset t1 = find(p.first);
        expr_offset t2 = find(p.second);
        m_eq_todo.pop_back();
        if (t1 == t2)
            continue;
        expr * n1 = t1.get_expr();
        expr * n2 = t2.get_expr();
        if (!is_app(n1) || !is_app(n2))
            return false;
        if (to_app(n1)->get_decl() != to_app(n2)->get_decl())
            return false;
        if (to_app(n1)->get_num_args() != to_app(n2)->get_num_args())
            return false;
        unsigned num = to_app(n1)->get_num_args();
        for (unsigned i = 0; i < num; i++) 
            m_eq_todo.push_back(expr_offset_pair(expr_offset(to_app(n1)->get_arg(i), t1.get_offset()),
                                                 expr_offset(to_app(n2)->get_arg(i), t2.get_offset())));
    }
    return true;
}

