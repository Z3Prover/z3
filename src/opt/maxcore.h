/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxsres.h

Abstract:
   
    Maxcore (weighted) max-sat algorithm by Nina and Bacchus, AAAI 2014.

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/

#pragma once

namespace opt {

    maxsmt_solver_base* mk_rc2(maxsat_context& c, unsigned id, vector<soft>& soft);

    maxsmt_solver_base* mk_rc2bin(maxsat_context& c, unsigned id, vector<soft>& soft);

    maxsmt_solver_base* mk_maxres(maxsat_context& c, unsigned id, vector<soft>& soft);

    maxsmt_solver_base* mk_maxres_binary(maxsat_context& c, unsigned id, vector<soft>& soft);

    maxsmt_solver_base* mk_primal_dual_maxres(maxsat_context& c, unsigned id, vector<soft>& soft);

};

