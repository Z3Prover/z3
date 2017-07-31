/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal_shared_occs.cpp

Abstract:

    Functor for computing the set of shared occurrences in a goal.

Author:

    Leonardo de Moura (leonardo) 2011-12-28

Revision History:

--*/
#include "tactic/goal_shared_occs.h"

void goal_shared_occs::operator()(goal const & g) {
    m_occs.reset();
    shared_occs_mark visited;
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * t = g.form(i);
        m_occs(t, visited);
    }
}
