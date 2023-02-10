
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_bounds.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/elim_bounds.h"


class elim_bounds_simplifier : public dependent_expr_simplifier {
    elim_bounds_rw m_rewriter;
    
public:
    elim_bounds_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m) {
    }

    char const* name() const override { return "cheap-fourier-motzkin"; }
        
    void reduce() override {
        if (!m_fmls.has_quantifiers())
            return;
        expr_ref r(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            if (!has_quantifiers(d.fml()))
                continue;
            m_rewriter(d.fml(), r);
            m_fmls.update(idx, dependent_expr(m, r, nullptr, d.dep()));
        }
    }
};

/*
  ADD_SIMPLIFIER("cheap-fourier-motzkin", "eliminate variables from quantifiers using partial Fourier-Motzkin elimination.", "alloc(elim_bounds_simplifier, m, p, s)")
 */
