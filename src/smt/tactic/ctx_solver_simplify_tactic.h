/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ctx_solver_simplify_tactic.h

Abstract:

    Context simplifier for propagating solver assignments.

Author:

    Nikolaj (nbjorner) 2012-3-6

Tactic Documentation:

## Tactic ctx-solver-simplify

### Short Description

A heavy handed version of `ctx-simplify`. It applies SMT checks on sub-formulas to check
if they can be simplified to `true` or `false` within their context.
Note that a sub-formula may occur within multiple contexts due to shared sub-terms.
In this case the tactic is partial and simplifies a limited number of context occurrences.


--*/
#pragma once

#include "tactic/tactical.h"

tactic * mk_ctx_solver_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("ctx-solver-simplify", "apply solver-based contextual simplification rules.", "mk_ctx_solver_simplify_tactic(m, p)")
*/

