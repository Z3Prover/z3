/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fu_malik.h

Abstract:

    Fu&Malik built-in optimization method.
    Adapted from sample code in C.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-15

Notes:

    Takes solver with hard constraints added.
    Returns a maximal satisfying subset of soft_constraints
    that are still consistent with the solver state.

--*/
#ifndef OPT_FU_MALIK_H_
#define OPT_FU_MALIK_H_

#include "opt_solver.h"
#include "maxsmt.h"

namespace opt {

    maxsmt_solver_base* mk_fu_malik(maxsat_context& c, weights_t & ws, expr_ref_vector const& soft);

    
};

#endif
