/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ambient_context.h

Abstract:

    Concrete `ambient_context_i` (ast/seq/seq_ambient_context.h) backed by
    a live `theory_seq` instance. This is the only place that bridges the
    ast/seq facet layer's dependency-tracker-based interface to
    `theory_seq`'s own bound-query methods.

    `is_var` is inherited as-is from `ambient_context_i` (concrete,
    non-virtual: `!u.str.is_power(e) && !u.str.is_unit(e)`); this class
    only supplies the base's `(ast_manager&, seq_util&)` constructor
    arguments from the live `theory_seq`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/seq/seq_ambient_context.h"
#include "ast/seq/seq_eq_facet.h"
#include "smt/theory_seq.h"

namespace seq {

    /**
     * `ambient_context_i` implementation wrapping a live `theory_seq`.
     * `theory_seq::lower_bound`/`upper_bound` do not currently return a
     * supporting justification (they are `const`, model-value-style
     * queries over the arithmetic theory), so - like
     * `sub_solver::implies` (smt/seq_solver_facet.cpp) folding a
     * whole unsat core into one dependency - bounds obtained this way are
     * reported with a `nullptr` dependency (an unconditional fact of the
     * ambient arithmetic theory's current state, not itself contingent on
     * any one branch's assumptions); this is sound (a `nullptr` dep is
     * always joinable/always "no extra justification needed") but not
     * maximally precise. Callers that need finer-grained provenance
     * should prefer a `dep_tracker`-carrying route (e.g. `solver_facet`'s
     * own incremental backend) where one exists.
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
            // No-op: theory_seq has no standalone "add_diseq_axiom" entry
            // point distinct from its ordinary disequality propagation
            // machinery; callers relying on this as a genuine axiom
            // injection point should use theory_seq's own internalization
            // path instead.
        }

        void add_axiom(expr_ref_vector const&) override {
            // No-op: theory_seq does not (yet) route any facet through
            // this ambient context's add_axiom - only theory_nseq's
            // stoi_facet currently uses it (see
            // smt/seq_nseq_ambient_context.h).
        }

        trail_stack& trail() override { return m_th.get_trail_stack(); }

    protected:
        // theory_seq has no eq_tree/dep_manager of its own (see class
        // comment above on lower_bound/upper_bound's nullptr deps) - a
        // conditional dependency here is reported the same way, as an
        // unconditional nullptr (sound, just less precise).
        eq_tree::dep_tracker mk_leaf_dep(unsigned) const override { return nullptr; }
    };

} // namespace seq
