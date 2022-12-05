/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    demodulator_tactic.h

Abstract:

    Tactic for solving variables

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/demodulator_simplifier.h"


class demodulator_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(demodulator_simplifier, m, p, s);
    }
};

inline tactic * mk_demodulator_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(demodulator_tactic_factory));
}

/*
  ADD_TACTIC("demodulator", "solve for variables.", "mk_demodulator_tactic(m, p)")
*/


