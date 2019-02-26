/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    for_each_expr.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-12-28.

Revision History:

--*/

#include "ast/for_each_expr.h"

struct expr_counter_proc {
    unsigned m_num;
    expr_counter_proc():m_num(0) {}
    void operator()(var * n)        { m_num++; }
    void operator()(app * n)        { m_num++; if (n->get_decl()->is_associative()) m_num += n->get_num_args() - 2; }
    void operator()(quantifier * n) { m_num++; }
};

unsigned get_num_exprs(expr * n, expr_mark & visited) {
    expr_counter_proc counter;
    for_each_expr(counter, visited, n);
    return counter.m_num;
}

unsigned get_num_exprs(expr * n, expr_fast_mark1 & visited) {
    expr_counter_proc counter;
    for_each_expr_core<expr_counter_proc, expr_fast_mark1, false, false>(counter, visited, n);
    return counter.m_num;
}

unsigned get_num_exprs(expr * n) {
    expr_fast_mark1 visited;
    return get_num_exprs(n, visited);
}

namespace has_skolem_functions_ns {
    struct found {}; 
    struct proc {
        void operator()(var * n) const {}
        void operator()(app const * n) const { if (n->get_decl()->is_skolem() && n->get_num_args() > 0) throw found(); }
        void operator()(quantifier * n) const {}
    };
};

bool has_skolem_functions(expr * n) {
    has_skolem_functions_ns::proc p;
    try {
        for_each_expr(p, n);
    }
    catch (const has_skolem_functions_ns::found &) {
        return true;
    }
    return false;
}
