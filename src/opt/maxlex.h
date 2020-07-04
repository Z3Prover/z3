/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxlex.h

Abstract:
   
    MaxLex solves weighted max-sat problems where weights impose lexicographic order.

Author:

    Nikolaj Bjorner (nbjorner) 2019-25-1

Notes:

--*/

#pragma once

namespace opt {

    bool is_maxlex(weights_t & ws);

    maxsmt_solver_base* mk_maxlex(maxsat_context& c, unsigned id, weights_t & ws, expr_ref_vector const& soft);


};

