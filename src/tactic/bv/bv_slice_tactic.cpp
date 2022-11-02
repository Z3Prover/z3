/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_slice_tactic.cpp

Abstract:

    Tactic for simplifying with bit-vector slices

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/

#include "ast/simplifiers/bv_slice.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "tactic/bv/bv_slice_tactic.h"


class bv_slice_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(bv::slice, m, s);
    }
};

tactic* mk_bv_slice_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(bv_slice_factory), "bv-slice");
}
