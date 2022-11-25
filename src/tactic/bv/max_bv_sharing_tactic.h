/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    max_bv_sharing_tactic.h

Abstract:

    Rewriter for "maximing" the number of shared terms.
    The idea is to rewrite AC terms to maximize sharing.
    This rewriter is particularly useful for reducing
    the number of Adders and Multipliers before "bit-blasting".

Author:

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/
#pragma once

#include "ast/simplifiers/max_bv_sharing.h"
#include "tactic/dependent_expr_state_tactic.h"

class max_bv_sharing_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return mk_max_bv_sharing(m, p, s);
    }
};

inline tactic* mk_max_bv_sharing_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(max_bv_sharing_tactic_factory), "max-bv-sharing");
}

/*
  ADD_TACTIC("max-bv-sharing", "use heuristics to maximize the sharing of bit-vector expressions such as adders and multipliers.", "mk_max_bv_sharing_tactic(m, p)")
*/


