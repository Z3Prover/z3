/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    fold_unfold_tactic.h

Abstract:

    Tactic for solving variables using fold/unfold transformations.

Author:

    Nikolaj Bjorner (nbjorner) 2025-11-05

Tactic Documentation:

## Tactic fold-unfold

### Short Description

Apply fold-unfold simplifications to solve for equalities


--*/

#pragma once
#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/fold_unfold.h"

inline tactic *mk_fold_unfold_tactic(ast_manager &m, params_ref const &p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto &m, auto &p, auto &s) -> dependent_expr_simplifier * { return alloc(euf::fold_unfold, m, s); });
}

/*
  ADD_TACTIC("fold-unfold", "solve for variables.", "mk_fold_unfold_tactic(m, p)")
  ADD_SIMPLIFIER("fold-unfold", "solve for variables.", "alloc(euf::fold_unfold, m, s)")
*/


