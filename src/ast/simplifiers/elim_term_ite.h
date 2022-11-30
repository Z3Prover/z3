
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_term_ite.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/elim_term_ite.h"


class elim_term_ite_simplifier : public dependent_expr_simplifier {
    elim_term_ite m_elim;
    
public:
    elim_term_ite_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_elim_term_ite(m) {
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
            m_rewriter(d.fml(), r);
            m_fmls.update(idx, dependent_expr(m, r, d.dep()));
        }
    }

    void push() override { dependent_expr_simplifier::push(); m_rewriter.push(); }
    
    void pop(unsigned n) override { dependent_expr_simplifier::pop(n); m_rewriter.pop(n); } 
};

