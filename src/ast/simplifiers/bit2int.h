
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bit2int.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/bit2int.h"


class bit2int_simplifier : public dependent_expr_simplifier {
    bit2int m_rewriter;
    
public:
    bit2int_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m) {
    }

    char const* name() const override { return "bit2int"; }
        
    void reduce() override {
        expr_ref r(m);
        proof_ref pr(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_rewriter(d.fml(), r, pr);
            m_fmls.update(idx, dependent_expr(m, r, mp(d.pr(), pr), d.dep()));
        }
    }

    bool supports_proofs() const override { return true; }
};

/*
  ADD_SIMPLIFIER("bit2int", "simplify bit2int expressions.", "alloc(bit2int_simplifier, m, p, s)")
 */
