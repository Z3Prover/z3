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
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/eliminate_predicates.h"


class eliminate_predicates_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(eliminate_predicates, m, s);
    }
};

inline tactic * mk_eliminate_predicates_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(eliminate_predicates_tactic_factory), "elim-predicates");
}

/*
  ADD_TACTIC("elim-predicates", "eliminate predicates.", "mk_eliminate_predicates_tactic(m, p)")
*/


