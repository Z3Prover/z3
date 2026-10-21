/*++
Copyright (c) 2026 Microsoft Corporation

Eliminate one-sided real variables through Boolean combinations of linear inequalities.
--*/
#pragma once

#include "ast/simplifiers/elim_monotone.h"
#include "tactic/dependent_expr_state_tactic.h"

inline tactic* mk_elim_monotone_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* { return alloc(elim_monotone, m, s); });
}

Z3_ADD_TACTIC(elim_monotone, "elim-monotone", "eliminate one-sided real variables from linear inequalities.", mk_elim_monotone_tactic(m, p));
Z3_ADD_SIMPLIFIER(elim_monotone, "elim-monotone", "eliminate one-sided real variables from linear inequalities.", alloc(elim_monotone, m, s));
