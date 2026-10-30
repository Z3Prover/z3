/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    finite_set_tactic.cpp

Abstract:

    See finite_set_tactic.h.

--*/
#include "ast/simplifiers/finite_set_simplifier.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "tactic/smtlogics/finite_set_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/tactical.h"

tactic* mk_finite_set_simplify_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
                     return alloc(finite_set_simplifier, m, p, s);
                 });
}

tactic* mk_finite_set_tactic(ast_manager& m, params_ref const& p) {
    return and_then(mk_finite_set_simplify_tactic(m, p), mk_smt_tactic(m, p));
}
