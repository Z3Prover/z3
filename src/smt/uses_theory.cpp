/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    uses_theory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-21.

Revision History:

--*/

#include"uses_theory.h"
#include"for_each_expr.h"

bool uses_theory(expr * n, family_id fid) {
    expr_mark visited;
    return uses_theory(n, fid, visited);
}

namespace uses_theory_ns {
    struct found {}; 
    struct proc {
        family_id m_fid;
        proc(family_id fid):m_fid(fid) {}
        void operator()(var * n) {}
        void operator()(app * n) { if (n->get_family_id() == m_fid) throw found(); }
        void operator()(quantifier * n) {}
    };
};

bool uses_theory(expr * n, family_id fid, expr_mark & visited) {
    uses_theory_ns::proc p(fid);
    try {
        for_each_expr(p, visited, n);
    }
    catch (uses_theory_ns::found) {
        return true;
    }
    return false;
}

