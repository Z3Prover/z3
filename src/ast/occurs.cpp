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

