/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_unconstr2_tactic.h

Abstract:

    Tactic for eliminating unconstrained terms.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/elim_unconstrained.h"
#include "ast/simplifiers/elim_unconstrained.h"

class elim_uncnstr2_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(elim_unconstrained, m, s);
    }
};

inline tactic * mk_elim_uncnstr2_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(elim_uncnstr2_tactic_factory), "elim-unconstr2");
}


/*
  ADD_TACTIC("elim-uncnstr2", "eliminate unconstrained variables.", "mk_elim_uncnstr2_tactic(m, p)")
*/


