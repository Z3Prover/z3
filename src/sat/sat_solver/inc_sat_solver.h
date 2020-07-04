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

#pragma once

#include "solver/solver.h"

class tactic;

solver* mk_inc_sat_solver(ast_manager& m, params_ref const& p, bool incremental_mode = true);

tactic* mk_psat_tactic(ast_manager& m, params_ref const& p);

/*
  ADD_TACTIC('psat', '(try to) solve goal using a parallel SAT solver.', 'mk_psat_tactic(m, p)')
*/

void  inc_sat_display(std::ostream& out, solver& s, unsigned sz, expr*const* soft, rational const* _weights);

