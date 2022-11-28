/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    propagate_values2_tactic.h

Abstract:

    Tactic for propagating equalities (= t v) where v is a value

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#include "util/params.h"
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/propagate_values.h"

class propagate_values2_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(propagate_values, m, p, s);
    }
};

inline tactic * mk_propagate_values2_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(propagate_values2_tactic_factory), "propagate-values2");
}


/*
  ADD_TACTIC("propagate-values2", "propagate constants.", "mk_propagate_values2_tactic(m, p)")
*/

