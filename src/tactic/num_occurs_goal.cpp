/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    num_occurs_goal.cpp

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#include"num_occurs_goal.h"
#include"goal.h"

void num_occurs_goal::operator()(goal const & g) {
    expr_fast_mark1   visited;
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        process(g.form(i), visited);
    }
}
