/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    card2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-20

--*/
#pragma once


#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/card2bv.h"

class card2bv_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(card2bv, m, p, s);
    }
};

inline tactic* mk_card2bv_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(card2bv_tactic_factory), "card2bv");
}

/*
  ADD_TACTIC("card2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_card2bv_tactic(m, p)")
*/


