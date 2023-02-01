/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    max_bv_sharing.cpp

Abstract:

    Rewriter for "maximing" the number of shared terms.
    The idea is to rewrite AC terms to maximize sharing.
    This rewriter is particularly useful for reducing
    the number of Adders and Multipliers before "bit-blasting".

Author

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/

#include "ast/rewriter/maximize_ac_sharing.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/rewriter_def.h"

class max_bv_sharing : public dependent_expr_simplifier {

    maximize_bv_sharing_rw m_rewriter;    
    unsigned               m_num_steps = 0;
        
public:
    max_bv_sharing(ast_manager & m, params_ref const & p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m) {
    }       

    void reset_statistics() override {
        m_num_steps = 0;
    }

    void collect_statistics(statistics& st) const override {
        st.update("max-sharing-steps", m_num_steps);
    }

    char const* name() const override { return "max-bv-sharing"; }

    void reduce() override {
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        for (unsigned idx : indices()) {
            auto [curr, p, d] = m_fmls[idx]();
            m_rewriter(curr, new_curr, new_pr);
            if (new_curr != curr) {
                m_num_steps += m_rewriter.get_num_steps();
                m_fmls.update(idx, dependent_expr(m, new_curr, mp(p, new_pr), d));
            }
        }
    }

    void push() override { dependent_expr_simplifier::push(); m_rewriter.push_scope(); }

    void pop(unsigned n) override { dependent_expr_simplifier::pop(n); m_rewriter.pop_scope(n); }
    
};

dependent_expr_simplifier * mk_max_bv_sharing(ast_manager & m, params_ref const & p, dependent_expr_state& fmls) {
    return alloc(max_bv_sharing, m, p, fmls);    
}

