/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_simplify_tactic.cpp

Abstract:

    Tactic simplifying prime-field goals and propagating constants (no
    certificates), preserving Boolean domain constraints ("ff-simplify").
    Implemented as a thin wrapper around ff_basic_simplifier (see
    ast/simplifiers/ff_simplify.h) via dependent_expr_state_tactic.

Author:

    Romain Soulat

--*/
#include "tactic/ff/ff_solve_tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/ff_simplify.h"

tactic *mk_ff_simplify_tactic(ast_manager &m, params_ref const &p) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](ast_manager &m, params_ref const &p, dependent_expr_state &s) -> dependent_expr_simplifier * {
                     return alloc(ff_basic_simplifier, m, p, s);
                 });
}
