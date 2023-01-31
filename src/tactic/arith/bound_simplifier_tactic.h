/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    bound_simplifier_tactic.h

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-22

Tactic Documentation:

## Tactic bound-simplifier

### Short Description

Tactic for simplifying arithmetical expressions modulo bounds

### Long Description

The tactic is used to eliminate occurrences of modulus expressions when it is known that terms are within the bounds
of the modulus.


--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/bound_simplifier.h"

inline tactic* mk_bound_simplifier_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(bound_simplifier, m, p, s); });
}

/*
  ADD_TACTIC("bound-simplifier", "Simplify arithmetical expressions modulo bounds.", "mk_bound_simplifier_tactic(m, p)")
  ADD_SIMPLIFIER("bound-simplifier", "Simplify arithmetical expressions modulo bounds.", "[](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(bound_simplifier, m, p, s); }")
*/
