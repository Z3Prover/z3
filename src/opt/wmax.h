/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    wmax.h

Abstract:

    Theory Solver based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/

#ifndef WMAX_H_
#define WMAX_H_

#include "maxsmt.h"

namespace opt {
    maxsmt_solver_base* mk_wmax(maxsat_context& c, weights_t & ws, expr_ref_vector const& soft);

}
#endif
