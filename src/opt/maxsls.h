/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsls.h

Abstract:

    Weighted SLS MAXSAT module

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

    Partial, one-round SLS optimizer. Finds the first 
    local maximum given a resource bound and returns.

--*/
#ifndef OPT_SLS_MAX_SAT_H_
#define OPT_SLS_MAX_SAT_H_

#include "maxsmt.h"

namespace opt {


    maxsmt_solver_base* mk_sls(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft);

    
};

#endif
