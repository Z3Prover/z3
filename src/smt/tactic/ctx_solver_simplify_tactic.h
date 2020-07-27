/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ctx_solver_simplify_tactic.h

Abstract:

    Context simplifier for propagating solver assignments.

Author:

    Nikolaj (nbjorner) 2012-3-6

Notes:

--*/
#pragma once

#include "tactic/tactical.h"

tactic * mk_ctx_solver_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("ctx-solver-simplify", "apply solver-based contextual simplification rules.", "mk_ctx_solver_simplify_tactic(m, p)")
*/

