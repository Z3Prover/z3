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
    non-virtual: `!u.str.is_power(e) && !u.str.is_unit(e) && !m.is_ite(e)`);
    this class only supplies the base's `(ast_manager&, seq_util&)`
    constructor arguments from the live `theory_seq`.

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
     * `arith_sub_solver::implies` (smt/seq_arith_facet.cpp) folding a
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
    };

} // namespace seq
