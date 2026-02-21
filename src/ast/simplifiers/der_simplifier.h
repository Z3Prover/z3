/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    der_simplifier.h

Abstract:

    Dependent expression simplifier for destructive equality resolution (DER).

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/der.h"

class der_simplifier : public dependent_expr_simplifier {
    der_rewriter m_r;
public:
    der_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls)
        : dependent_expr_simplifier(m, fmls), m_r(m) {}

    char const* name() const override { return "der"; }

    void reduce() override {
        expr_ref  new_curr(m);
        proof_ref new_pr(m);
        for (unsigned idx : indices()) {
            auto d = m_fmls[idx];
            m_r(d.fml(), new_curr, new_pr);
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));
        }
    }

    bool supports_proofs() const override { return true; }
};
