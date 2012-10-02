/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_weight.h

Abstract:

    Functor for computing the weight of an expression.

Author:

    Leonardo (leonardo) 2008-01-11

Notes:

--*/
#ifndef _EXPR_WEIGHT_H_
#define _EXPR_WEIGHT_H_

#include"recurse_expr.h"
#include"approx_nat.h"

typedef approx_nat weight;

struct expr_weight_visitor {
    weight visit(var * n) { return weight(1); }
    weight visit(app const * n, weight const * args);
    weight visit(quantifier * n, weight body, weight *, weight *) { body += 1; return body; } 
};

typedef recurse_expr<weight, expr_weight_visitor, true> expr_weight;

#endif /* _EXPR_WEIGHT_H_ */
