/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    pull_nested_quantifiers.h

Abstract:

    pull nested quantifiers

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/normal_forms/pull_quant.h"


class pull_nested_quantifiers_simplifier : public dependent_expr_simplifier {
    pull_nested_quant      m_pull;

public:
    pull_nested_quantifiers_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_pull(m) {
    }

    char const* name() const override { return "pull-nested-quantifiers"; }
        
    void reduce() override {
        if (!m_fmls.has_quantifiers())
            return;
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        for (unsigned idx : indices()) {
            auto d = m_fmls[idx];
            m_pull(d.fml(), new_curr, new_pr);
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));
        }
    }

    bool supports_proofs() const override { return true; }
};

/*
  ADD_SIMPLIFIER("pull-nested-quantifiers", "pull nested quantifiers to top-level.", "alloc(pull_nested_quantifiers_simplifier, m, p, s)")
*/
