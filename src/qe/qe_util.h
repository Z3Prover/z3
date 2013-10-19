/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    qe_util.h

Abstract:

    Utilities for quantifiers.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#ifndef _QE_UTIL_H_
#define _QE_UTIL_H_

#include "ast.h"

namespace qe {
    /**
       \brief Collect top-level conjunctions and disjunctions.
    */
    void flatten_and(expr_ref_vector& result);

    void flatten_and(expr* fml, expr_ref_vector& result);

    void flatten_or(expr_ref_vector& result);

    void flatten_or(expr* fml, expr_ref_vector& result);

    expr_ref mk_and(expr_ref_vector const& fmls);

    expr_ref mk_or(expr_ref_vector const& fmls);

}
#endif
