
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    distribute_forall.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/distribute_forall.h"


class distribute_forall_simplifier : public dependent_expr_simplifier {
    distribute_forall m_dist;
    
public:
    distribute_forall_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_dist(m) {
    }

    char const* name() const override { return "distribute-forall"; }
        
    void reduce() override {
        if (!m_fmls.has_quantifiers())
            return;
        expr_ref r(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            if (!has_quantifiers(d.fml()))
                continue;
            m_dist(d.fml(), r);
            m_fmls.update(idx, dependent_expr(m, r, nullptr, d.dep()));
        }
    }
};

