/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    num_occurs_assertion_set.cpp

Abstract:

    TODO: delete

Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#include"num_occurs_assertion_set.h"
#include"assertion_set.h"

// TODO delete
void num_occurs_as::operator()(assertion_set const & s) {
    expr_fast_mark1   visited;
    unsigned sz = s.size();
    for (unsigned i = 0; i < sz; i++) {
        process(s.form(i), visited);
    }
}
