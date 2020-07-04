/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxsres.h

Abstract:
   
    MaxRes (weighted) max-sat algorithm by Nina and Bacchus, AAAI 2014.

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/

#pragma once

namespace opt {

    maxsmt_solver_base* mk_maxres(maxsat_context& c, unsigned id, weights_t & ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_primal_dual_maxres(maxsat_context& c, unsigned id, weights_t & ws, expr_ref_vector const& soft);

};

