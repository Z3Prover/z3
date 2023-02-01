/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    rewriter_simplifier.h

Abstract:

    rewriter simplifier

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"


class rewriter_simplifier : public dependent_expr_simplifier {

    unsigned               m_num_steps = 0;
    params_ref             m_params;
    th_rewriter            m_rewriter;

public:
    rewriter_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m) {
        updt_params(p);
    }

    char const* name() const override { return "simplifier"; }
        
    void reduce() override {
        m_num_steps = 0;
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        for (unsigned idx : indices()) {
            auto d = m_fmls[idx];
            m_rewriter(d.fml(), new_curr, new_pr);
            m_num_steps += m_rewriter.get_num_steps();
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));            
        }
    }
    bool supports_proofs() const override { return true; }
    void collect_statistics(statistics& st) const override { st.update("simplifier-steps", m_num_steps); }
    void reset_statistics() override { m_num_steps = 0; }
    void updt_params(params_ref const& p) override { m_params.append(p); m_rewriter.updt_params(m_params); }
    void collect_param_descrs(param_descrs& r) override { th_rewriter::get_param_descrs(r); }
};

/*
  ADD_SIMPLIFIER("simplify", "apply simplification rules.", "alloc(rewriter_simplifier, m, p, s)")
 */
