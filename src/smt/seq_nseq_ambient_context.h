/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nseq_ambient_context.h

Abstract:

    `ambient_context_i` implementation backed by a live `theory_nseq`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/seq/seq_ambient_context.h"
#include "ast/seq/seq_eq_facet.h"
#include "smt/theory_nseq.h"

namespace seq {

    class theory_nseq_ambient_context : public ambient_context_i<eq_tree::dep_tracker> {
        smt::theory_nseq& m_th;
    public:
        explicit theory_nseq_ambient_context(smt::theory_nseq& th)
            : ambient_context_i<eq_tree::dep_tracker>(th.get_manager(), th.m_seq), m_th(th) {}

        bool lower_bound(expr* e, rational& lo, eq_tree::dep_tracker& dep) override {
            dep = nullptr;
            if (!m_th.lower_bound(e, lo))
                return false;
            dep = add_conditional_dep(m_th.m_autil.mk_ge(e, m_th.m_autil.mk_int(lo)));
            return true;
        }

        bool upper_bound(expr* e, rational& hi, eq_tree::dep_tracker& dep) override {
            dep = nullptr;
            if (!m_th.upper_bound(e, hi))
                return false;
            dep = add_conditional_dep(m_th.m_autil.mk_le(e, m_th.m_autil.mk_int(hi)));
            return true;
        }

        bool current_value(expr* e, rational& v) override {
            return m_th.get_num_value(e, v);
        }

        theory_seq_params const& fparams() const override { return m_th.ctx.get_fparams(); }

        eq_tree::dep_tracker literal_if_false(expr* e) override {
            if (!m_th.ctx.b_internalized(e))
                return nullptr;
            smt::literal lit = m_th.ctx.get_literal(e);
            if (m_th.ctx.get_assignment(lit) != l_false)
                return nullptr;
            return add_conditional_dep(m.mk_not(e));
        }

        void add_diseq_axiom(expr*, expr*) override {
            // No-op: no standalone axiom-injection entry point distinct from
            // theory_nseq's ordinary disequality propagation.
        }

        // Reuse seq_axioms' ordinary clause-to-theory-axiom path.
        void add_axiom(expr_ref_vector const& clause) override {
            m_th.m_ax.add_axiom_clause(clause);
        }

        trail_stack& trail() override { return m_th.m_tree.trail(); }

    protected:
        eq_tree::dep_tracker mk_leaf_dep(unsigned idx) const override {
            return m_th.m_tree.dep_mgr().mk_leaf(idx);
        }
    };

} // namespace seq
