/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    used_vars.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/

#include "ast/used_vars.h"

void used_vars::process(expr * n, unsigned delta) {
    unsigned j, idx;

    if (m_num_found_vars == m_num_decls)
        return;

    m_cache.reset();
    m_todo.reset();
    m_todo.push_back(expr_delta_pair(n, delta));

    while (!m_todo.empty()) {
        expr_delta_pair const & p = m_todo.back();

        n     = p.m_node;

        if (n->get_ref_count() > 1 && m_cache.contains(p)) {
            m_todo.pop_back();
            continue;
        }
        
        if (n->get_ref_count() > 1) {
            // cache only shared and non-constant nodes
            m_cache.insert(p);
        }

        delta = p.m_delta;
        m_todo.pop_back();
        
        switch (n->get_kind()) {
        case AST_APP:
            j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                expr * arg = to_app(n)->get_arg(j);
                m_todo.push_back(expr_delta_pair(arg, delta));
            }
            break;
        case AST_VAR:
            idx = to_var(n)->get_idx();
            if (idx >= delta) {
                idx = idx - delta;
                if (idx >= m_found_vars.size())
                    m_found_vars.resize(idx + 1, nullptr);
                if (!m_found_vars[idx]) {
                    m_found_vars[idx] = to_var(n)->get_sort();
                    if (idx < m_num_decls)
                        m_num_found_vars++;
                    if (m_num_found_vars == m_num_decls) {
                        m_todo.reset();
                        return;
                    }
                }
            }
            break;
        case AST_QUANTIFIER:
            // recurse so that memoization is correct with respect to 'delta'.
            delta += to_quantifier(n)->get_num_decls();
            j      = to_quantifier(n)->get_num_patterns();
            while (j > 0) {
                --j;
                m_todo.push_back(expr_delta_pair(to_quantifier(n)->get_pattern(j), delta));
            }
            j      = to_quantifier(n)->get_num_no_patterns();
            while (j > 0) {
                --j;
                m_todo.push_back(expr_delta_pair(to_quantifier(n)->get_no_pattern(j), delta));
            }
            m_todo.push_back(expr_delta_pair(to_quantifier(n)->get_expr(), delta));
            break;
        default:
            break;
        }
    }
}

bool used_vars::uses_all_vars(unsigned num_decls) const {
    if (num_decls > m_found_vars.size())
        return false;
    for (unsigned i = 0; i < num_decls; i++) {
        if (!m_found_vars[i])
            return false;
    }
    return true;
}

bool used_vars::uses_a_var(unsigned num_decls) const {
    num_decls = std::min(num_decls, m_found_vars.size());
    for (unsigned i = 0; i < num_decls; i++) {
        if (m_found_vars[i])
            return true;
    }
    return false;
}

unsigned used_vars::get_num_vars() const {
    unsigned r   = 0;
    unsigned num = m_found_vars.size();
    for (unsigned i = 0; i < num; i++) {
        if (m_found_vars[i])
            r++;
    }
    return r;
}
