/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    inc_sat_solver.h

Abstract:

    incremental solver based on SAT core.

Author:

    Nikolaj Bjorner (nbjorner) 2014-7-30

Notes:

--*/

#ifndef _HS_INC_SAT_SOLVER_H_
#define _HS_INC_SAT_SOLVER_H_

#include "solver.h"

solver* mk_inc_sat_solver(ast_manager& m, params_ref const& p);

void set_soft_inc_sat(solver* s, unsigned sz, expr*const* soft, rational const* weights);

#endif
