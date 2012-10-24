/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_weight.cpp

Abstract:

    Functor for computing the weight of an expression.

Author:

    Leonardo (leonardo) 2008-01-11

Notes:

--*/
#include"expr_weight.h"
#include"recurse_expr_def.h"

template class recurse_expr<weight, expr_weight_visitor, true>;

weight expr_weight_visitor::visit(app const * n, weight const * args) {
    weight r(1);
    unsigned j = n->get_num_args();
    while (j > 0) {
        --j;
        r += args[j];
    }
    return r;
}
