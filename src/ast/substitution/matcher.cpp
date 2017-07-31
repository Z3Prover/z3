/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    matcher.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#include "ast/substitution/matcher.h"

bool matcher::operator()(expr * e1, expr * e2, substitution & s) {
    reset();
    m_subst = &s;
    m_todo.push_back(expr_pair(e1, e2));
    while (!m_todo.empty()) {
        expr_pair const & p = m_todo.back();
        // if (m_cache.contains(p)) {
        //    m_todo.pop_back();
        //    continue;
        // }

        if (is_var(p.first)) {
            expr_offset r;
            if (m_subst->find(to_var(p.first), 0, r)) {
                if (r.get_expr() != p.second)
                    return false;
            }
            else {
                m_subst->insert(to_var(p.first), 0, expr_offset(p.second, 1));
            }
            m_todo.pop_back();
            continue;
        }


        if (is_var(p.second))
            return false;
        if (!is_app(p.first))
            return false;
        if (!is_app(p.second))
            return false;

        app * n1 = to_app(p.first);
        app * n2 = to_app(p.second);

        if (n1->get_decl() != n2->get_decl())
            return false;

        unsigned num_args1 = n1->get_num_args();
        if (num_args1 != n2->get_num_args())
            return false;

        m_todo.pop_back();

        if (num_args1 == 0)
            continue;
        
        // m_cache.insert(p);
        unsigned j = num_args1;
        while (j > 0) {
            --j;
            m_todo.push_back(expr_pair(n1->get_arg(j), n2->get_arg(j)));
        }
    }
    return true;
}

void matcher::reset() {
    // m_cache.reset();
    m_todo.reset();
}
