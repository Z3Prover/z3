/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    eliminate_predicates_tactic.h

Abstract:

    Tactic for eliminating macros and predicates

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/
#pragma once

#include "util/params.h"
#include "ast/simplifiers/eliminate_predicates.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"

inline tactic * mk_eliminate_predicates_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(eliminate_predicates, m, s); });
}

/*
  ADD_TACTIC("elim-predicates", "eliminate predicates.", "mk_eliminate_predicates_tactic(m, p)")
*/
