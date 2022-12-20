/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_smt_solver.h

Abstract:

    incremental solver based on SAT core.

Author:

    Nikolaj Bjorner (nbjorner) 2014-7-30

Notes:

--*/

#pragma once

#include "solver/solver.h"

solver* mk_sat_smt_solver(ast_manager& m, params_ref const& p);

