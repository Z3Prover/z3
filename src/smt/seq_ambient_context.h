/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ambient_context.h

Abstract:

    `ambient_context_i` implementation backed by a live `theory_seq`.
    It bridges the facet layer's dependency-tracker interface to
    `theory_seq`'s bound and value queries.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/seq/seq_ambient_context.h"
#include "ast/seq/seq_eq_facet.h"
#include "smt/theory_seq.h"

namespace seq {

    /**
     * Wraps a live `theory_seq`.
     * Bound queries do not expose supporting justifications, so they
     * report `nullptr` dependencies: sound, but less precise than a
     * dependency-carrying query path.
     */
    class theory_seq_ambient_context : public ambient_context_i<eq_tree::dep_tracker> {
        smt::theory_seq& m_th;
    public:
        explicit theory_seq_ambient_context(smt::theory_seq& th)
            : ambient_context_i<eq_tree::dep_tracker>(th.get_manager(), th.m_util), m_th(th) {}

        bool lower_bound(expr* e, rational& lo, eq_tree::dep_tracker& dep) override {
            dep = nullptr;
            return m_th.lower_bound(e, lo);
        }

        bool upper_bound(expr* e, rational& hi, eq_tree::dep_tracker& dep) override {
            dep = nullptr;
            return m_th.upper_bound(e, hi);
        }

        bool current_value(expr* e, rational& v) override {
            return m_th.get_num_value(e, v);
        }

        theory_seq_params const& fparams() const override { return m_th.get_fparams(); }

        eq_tree::dep_tracker literal_if_false(expr*) override {
            // Not currently exposed by theory_seq; conservatively unknown.
            return nullptr;
        }

        void add_diseq_axiom(expr*, expr*) override {
            // No-op: theory_seq has no separate disequality-axiom hook.
        }

        void add_axiom(expr_ref_vector const&) override {
            // No-op: theory_seq does not route facet axioms through this interface.
        }

        trail_stack& trail() override { return m_th.get_trail_stack(); }

    protected:
        // theory_seq has no eq_tree dependency manager, so conditional
        // dependencies are reported as `nullptr`.
        eq_tree::dep_tracker mk_leaf_dep(unsigned) const override { return nullptr; }
    };

} // namespace seq
