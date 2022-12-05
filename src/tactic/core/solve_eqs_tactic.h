/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs_tactic.h

Abstract:

    Tactic for solving variables

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/solve_eqs.h"

inline tactic * mk_solve_eqs_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(euf::solve_eqs, m, s); });
}

/*
  ADD_TACTIC("solve-eqs", "solve for variables.", "mk_solve_eqs_tactic(m, p)")
*/
