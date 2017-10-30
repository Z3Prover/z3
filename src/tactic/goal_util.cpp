/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal_util.cpp

Abstract:

    goal goodies.

Author:

    Leonardo de Moura (leonardo) 2012-01-03.

Revision History:

--*/
#include "tactic/goal_util.h"
#include "tactic/goal.h"

struct has_term_ite_functor {
    struct found {};
    ast_manager & m;
    has_term_ite_functor(ast_manager & _m):m(_m) {}
    void operator()(var *) {}
    void operator()(quantifier *) {}
    void operator()(app * n) { if (m.is_term_ite(n)) throw found(); }
};

bool has_term_ite(goal const & g) {
    return test<has_term_ite_functor>(g);
}
