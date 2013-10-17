/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    weighted_maxsat.h

Abstract:
    Weighted MAXSAT module

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/

#include "weighted_maxsat.h"

namespace opt {
    /**
       Takes solver with hard constraints added.
       Returns a maximal satisfying subset of weighted soft_constraints
       that are still consistent with the solver state.
    */
    
    lbool weighted_maxsat(solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights) {
        NOT_IMPLEMENTED_YET();
        return l_false;
    }
};

