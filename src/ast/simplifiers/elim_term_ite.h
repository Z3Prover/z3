
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_term_ite.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/normal_forms/elim_term_ite.h"


class elim_term_ite_simplifier : public dependent_expr_simplifier {
    defined_names    m_df;
    elim_term_ite_rw m_rewriter;

public:
    elim_term_ite_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_df(m),
        m_rewriter(m, m_df) {
    }

    char const* name() const override { return "elim-term-ite"; }
        
    void reduce() override {
        expr_ref r(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_rewriter(d.fml(), r);
            m_fmls.update(idx, dependent_expr(m, r, d.dep()));
        }
    }

    void push() override { dependent_expr_simplifier::push(); m_df.push(); m_rewriter.push(); }
    
    void pop(unsigned n) override { m_rewriter.pop(n); m_df.pop(n); dependent_expr_simplifier::pop(n); }
};

