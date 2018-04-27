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

#ifndef HS_INC_SAT_SOLVER_H_
#define HS_INC_SAT_SOLVER_H_

#include "solver/solver.h"

class tactic;

solver* mk_inc_sat_solver(ast_manager& m, params_ref const& p, bool incremental_mode = true);

tactic* mk_psat_tactic(ast_manager& m, params_ref const& p);


void  inc_sat_display(std::ostream& out, solver& s, unsigned sz, expr*const* soft, rational const* _weights);

#endif
