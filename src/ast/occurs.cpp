/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    occurs.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-07.

Revision History:

--*/
#include "ast/occurs.h"

#include "ast/for_each_expr.h"
#include "ast/for_each_ast.h"

// -----------------------------------
//
// Occurs check
//
// -----------------------------------

namespace {
    struct found {}; 
    
    struct proc {
        expr * m_n;

#define CHECK() { if (n == m_n) throw found(); }

        proc(expr * n):m_n(n) {}
        void operator()(var const * n) { CHECK(); }
        void operator()(app const * n) { CHECK(); }
        void operator()(quantifier const * n) { CHECK(); }
    };

    struct decl_proc {
        func_decl * m_d;

        decl_proc(func_decl * d):m_d(d) {}
        void operator()(var const * n) { }
        void operator()(app const * n) { if (n->get_decl() == m_d) throw found(); }
        void operator()(quantifier const * n) { }
    };


    struct sort_proc {
        sort* m_s;
        sort_proc(sort* s) :m_s(s) {}
        void operator()(sort const* s2) { if (m_s == s2) throw found(); }
        void operator()(ast*) {}
    };


}

// Return true if n1 occurs in n2
bool occurs(expr * n1, expr * n2) {
    proc p(n1);
    try {
        quick_for_each_expr(p, n2);
    }
    catch (const found &) {
        return true;
    }
    return false;
}

bool occurs(func_decl * d, expr * n) {
    decl_proc p(d);
    try {
        quick_for_each_expr(p, n);
    }
    catch (const found &) {
        return true;
    }
    return false;
}

bool occurs(sort* s1, sort* s2) {
    sort_proc p(s1);
    try {
        for_each_ast(p, s2, true);
    }
    catch (const found&) {
        return true;
    }
    return false;
}

void mark_occurs(ptr_vector<expr>& to_check, expr* v, expr_mark& occ) {
    expr_fast_mark2 visited;
    occ.mark(v, true);
    visited.mark(v, true);
    while (!to_check.empty()) {
        expr* e = to_check.back();
        if (visited.is_marked(e)) {
            to_check.pop_back();
            continue;
        }
        if (is_app(e)) {
            bool does_occur = false;
            bool all_visited = true;
            for (expr* arg : *to_app(e)) {
                if (!visited.is_marked(arg)) {
                    to_check.push_back(arg);
                    all_visited = false;
                }
                else 
                    does_occur |= occ.is_marked(arg);                
            }
            if (all_visited) {
                occ.mark(e, does_occur);
                visited.mark(e, true);
                to_check.pop_back();
            }
        }
        else if (is_quantifier(e)) {
            expr* body = to_quantifier(e)->get_expr();
            if (visited.is_marked(body)) {
                visited.mark(e, true);
                occ.mark(e, occ.is_marked(body));
                to_check.pop_back();
            }
            else 
                to_check.push_back(body);            
        }
        else {
            visited.mark(e, true);
            to_check.pop_back();
        }
    }
}
