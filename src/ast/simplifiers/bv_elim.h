/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_elim.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/bv_elim.h"


namespace bv {
class elim_simplifier : public dependent_expr_simplifier {
    bv_elim_rw m_rewriter;
    
public:
    elim_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m) {
    }

    char const* name() const override { return "bv-elim"; }
        
    void reduce() override {
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
}
