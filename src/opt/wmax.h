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

#pragma once

#include "opt/maxsmt.h"

namespace opt {
    maxsmt_solver_base* mk_wmax(maxsat_context& c, weights_t & ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_sortmax(maxsat_context& c, weights_t & ws, expr_ref_vector const& soft);

}
