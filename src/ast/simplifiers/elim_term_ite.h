
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
        proof_ref pr(m);
        unsigned prev_defs_sz = m_rewriter.new_defs().size();
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_rewriter(d.fml(), r, pr);
            if (d.fml() != r)
                m_fmls.update(idx, dependent_expr(m, r, mp(d.pr(), pr), d.dep()));
            for (unsigned i = prev_defs_sz; i < m_rewriter.new_defs().size(); ++i) {
                auto const& def = m_rewriter.new_defs()[i];
                m_fmls.add(dependent_expr(m, def.fml(), def.pr(), nullptr));
            }
            prev_defs_sz = m_rewriter.new_defs().size();
        }
    }

    bool supports_proofs() const override { return true; }

    void push() override { dependent_expr_simplifier::push(); m_df.push(); m_rewriter.push(); }
    
    void pop(unsigned n) override { m_rewriter.pop(n); m_df.pop(n); dependent_expr_simplifier::pop(n); }

    void translate(dependent_expr_simplifier& other) override {
        auto& dst = dynamic_cast<elim_term_ite_simplifier&>(other);
        m_df.translate(dst.m_df, translation());
    }
};

/*
  ADD_SIMPLIFIER("elim-term-ite", "eliminate if-then-else term by hoisting them top top-level.", "alloc(elim_term_ite_simplifier, m, p, s)")
*/
