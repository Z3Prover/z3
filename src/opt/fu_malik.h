/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fu_malik.h

Abstract:
    Fu&Malik built-in optimization method.
    Adapted from sample code.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-15

Notes:

--*/
#ifndef _OPT_FU_MALIK_H_
#define _OPT_FU_MALIK_H_

#include "solver.h"

namespace opt {
    /**
       takes solver with hard constraints added.
       Returns a maximal satisfying subset of soft_constraints
       that are still consistent with the solver state.
    */
    
    lbool fu_malik_maxsat(solver& s, expr_ref_vector& soft_constraints);
};

#endif
