/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr_stat.cpp

Abstract:

    Expression statistics (symbol count, var count, depth, ...)
    
    All functions in these module assume expressions do not contain
    nested quantifiers.
    
Author:

    Leonardo de Moura (leonardo) 2008-02-05.

Revision History:

--*/
#include"for_each_expr.h"
#include"expr_stat.h"

void get_expr_stat(expr * n, expr_stat & r) {
    typedef std::pair<expr *, unsigned> pair;
    buffer<pair> todo;
    todo.push_back(pair(n, 0));
    while (!todo.empty()) {
        pair & p       = todo.back();
        n              = p.first;
        unsigned depth = p.second;
        unsigned j;
        todo.pop_back();
        r.m_sym_count++;
        if (depth > r.m_depth)
            r.m_depth = depth;
        switch (n->get_kind()) {
        case AST_APP:
            j = to_app(n)->get_num_args();
            if (j == 0)
                r.m_const_count++;
            while (j > 0) {
                --j;
                todo.push_back(pair(to_app(n)->get_arg(j), depth + 1));
            }
            break;
        case AST_VAR:
            if (to_var(n)->get_idx() > r.m_max_var_idx) 
                r.m_max_var_idx = to_var(n)->get_idx();
            r.m_ground = false;
            break;
        case AST_QUANTIFIER:
            todo.push_back(pair(to_quantifier(n)->get_expr(), depth+1));
            break;
        default:
            UNREACHABLE();
        }
    }
}

unsigned get_symbol_count(expr * n) {
    unsigned r = 0;
    ptr_buffer<expr> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        n = todo.back();
        unsigned j;
        todo.pop_back();
        r++;
        switch (n->get_kind()) {
        case AST_APP:
            j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                todo.push_back(to_app(n)->get_arg(j));
            }
            break;
        case AST_QUANTIFIER:
            todo.push_back(to_quantifier(n)->get_expr());
            break;
        default:
            break;
        }
    }
    return r;
}

