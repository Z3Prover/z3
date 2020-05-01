/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal_num_occurs.cpp

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#include "tactic/goal_num_occurs.h"
#include "tactic/goal.h"

void goal_num_occurs::operator()(goal const & g) {
    expr_fast_mark1   visited;
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        m_pinned.push_back(g.form(i));
        process(g.form(i), visited);
    }
}
