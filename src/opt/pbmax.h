/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    pbmax.h

Abstract:

    MaxSAT based on pb theory.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/

#ifndef _PBMAX_H_
#define _PBMAX_H_

#include "maxsmt.h"

namespace opt {
    maxsmt_solver_base* mk_pbmax(context& c,
                               vector<rational> const& ws, expr_ref_vector const& soft);

}
#endif
