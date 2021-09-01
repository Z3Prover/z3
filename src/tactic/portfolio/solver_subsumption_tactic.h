/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver_subsumption_tactic.h

Author:

    Nikolaj Bjorner (nbjorner) 2021-7-23

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_solver_subsumption_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("solver-subsumption", "remove assertions that are subsumed.", "mk_solver_subsumption_tactic(m, p)")
*/


