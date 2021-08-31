/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    recurse_expr_def.h

Abstract:

    Traverse an expression applying a visitor.

Author:

    Leonardo de Moura (leonardo) 2008-01-11.

Revision History:

--*/
#pragma once

#include "ast/recurse_expr.h"

template<typename T, typename Visitor, bool IgnorePatterns, bool CallDestructors>
inline void recurse_expr<T, Visitor, IgnorePatterns, CallDestructors>::visit(expr * n, bool & visited) {
    if (!is_cached(n)) {
        m_todo.push_back(n);
        visited = false;
    }
}

template<typename T, typename Visitor, bool IgnorePatterns, bool CallDestructors>
bool recurse_expr<T, Visitor, IgnorePatterns, CallDestructors>::visit_children(expr * n) {
    bool visited = true;
    unsigned num;
    switch (n->get_kind()) {
    case AST_APP:
        num = to_app(n)->get_num_args();
        for (unsigned j = 0; j < num; j++) 
            visit(to_app(n)->get_arg(j), visited);
        break;
    case AST_QUANTIFIER:
        if (!IgnorePatterns) {
            num = to_quantifier(n)->get_num_patterns();
            for (unsigned j = 0; j < num; j++)
                visit(to_quantifier(n)->get_pattern(j), visited);
            num = to_quantifier(n)->get_num_no_patterns();
            for (unsigned j = 0; j < num; j++)
                visit(to_quantifier(n)->get_no_pattern(j), visited);
        }
        visit(to_quantifier(n)->get_expr(), visited);
        break;
    default:
        break;
    }
    return visited;
}

template<typename T, typename Visitor, bool IgnorePatterns, bool CallDestructors>
void recurse_expr<T, Visitor, IgnorePatterns, CallDestructors>::process(expr * n) {
    unsigned num;
    switch (n->get_kind()) {
    case AST_APP:
        m_results1.reset();
        num = to_app(n)->get_num_args();
        for (unsigned j = 0; j < num; j++)
            m_results1.push_back(get_cached(to_app(n)->get_arg(j)));
        cache_result(n, this->Visitor::visit(to_app(n), m_results1.data()));
        break;
    case AST_VAR: 
        cache_result(n, this->Visitor::visit(to_var(n)));
        break;
    case AST_QUANTIFIER:  
        if (IgnorePatterns) {
            cache_result(n, this->Visitor::visit(to_quantifier(n), get_cached(to_quantifier(n)->get_expr()), nullptr, nullptr));
        }
        else {
            m_results1.reset();
            m_results2.reset();
            num = to_quantifier(n)->get_num_patterns();
            for (unsigned j = 0; j < num; j++)
                m_results1.push_back(get_cached(to_quantifier(n)->get_pattern(j)));
            num = to_quantifier(n)->get_num_no_patterns();
            for (unsigned j = 0; j < num; j++)
                m_results2.push_back(get_cached(to_quantifier(n)->get_no_pattern(j)));
            cache_result(n, this->Visitor::visit(to_quantifier(n), get_cached(to_quantifier(n)->get_expr()), m_results1.data(), m_results2.data()));
        }
        break;
    default: 
        UNREACHABLE();
    }
}

template<typename T, typename Visitor, bool IgnorePatterns, bool CallDestructors>
T recurse_expr<T, Visitor, IgnorePatterns, CallDestructors>::operator()(expr * r) {
    m_todo.push_back(r);
    while (!m_todo.empty()) {
        expr * n = m_todo.back();
        if (is_cached(n))
            m_todo.pop_back();
        else if (visit_children(n)) {
            m_todo.pop_back();
            process(n);
        }
    }
    return get_cached(r);
}

