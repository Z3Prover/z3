/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxhs.h

Abstract:

    HS-max based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/

#ifndef HS_MAX_H_
#define HS_MAX_H_

#include "maxsmt.h"

namespace opt {
    maxsmt_solver_base* mk_maxhs(maxsat_context& c,
                                 weights_t& ws, expr_ref_vector const& soft);
}
#endif
