/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_lex_facet.h

Abstract:

    Lexicographic comparison facet: `str.<` / `str.<=`.

    Obligations are stored as token vectors. Propagation strips known
    equal prefixes, resolves comparisons once one side is exhausted or
    two leading constant characters differ, and leaves variable-led
    cases pending for later substitutions.

    Resolution rules (`is_strict` records whether `str.<` (true) or
    `str.<=` (false) was asserted for a `(lhs, rhs)` pair):
      - Strip every leading pair of tokens that are already known equal
        (same ast pointer, or - for two unit/character constants - equal
        constants) from both sides; this is always sound regardless of
        `is_strict` (it can never change the comparison's outcome).
      - If afterwards both sides are simultaneously empty: `lhs == rhs`,
        so the obligation holds iff `!is_strict` - conflict if
        `is_strict`, discharge otherwise.
      - If `lhs` is empty and `rhs` is not (or vice versa): the shorter,
        now-empty side is a proper prefix of the other (lexicographic
        order over sequences treats shorter-and-a-prefix as strictly
        smaller, matching `theory_seq`'s `pref12`/`pref21` disjuncts) -
        discharge if the empty side is `lhs` for both `is_strict` and
        `!is_strict` (empty is always `<=`, and strictly `<` whenever
        `rhs` is nonempty, which holds here), else (empty side is `rhs`)
        conflict.
      - If both leading tokens are unit/character constants that are
        distinct constants: the comparison is decided outright by
        comparing the two constant values - discharge if consistent with
        `is_strict`'s direction, conflict otherwise.
      - Otherwise the obligation stays pending until more substitutions
        or equalities resolve its leading tokens.

    `detect_cycles` uses an incremental `euf::egraph` to collapse
    semantically equal sides and detect cycles among pending
    obligations.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/euf/euf_egraph.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    // One pending lexicographic-order obligation over token vectors.
    struct str_lex {
        expr_ref_vector      m_lhs;
        expr_ref_vector      m_rhs;
        bool                 m_strict;
        eq_tree::dep_tracker m_dep;
        str_lex(expr_ref_vector const& lhs, expr_ref_vector const& rhs, bool strict, eq_tree::dep_tracker dep = nullptr) :
            m_lhs(lhs), m_rhs(rhs), m_strict(strict), m_dep(dep) {}
    };

    /**
     * Facet holding a set of pending lexicographic-comparison
     * obligations. See module comment for the propagation
     * responsibilities.
     */
    class lex_facet : public stx::facet_i, public subst_sink_i {
        ast_manager& m;
        seq_util&    u;
        eq_tree::dep_manager_t& m_dm;
        vector<str_lex> m_lexs;

        // Incremental egraph used to collapse semantically equal sides
        // during cycle detection.
        euf::egraph m_g;
        // First eq/deq entry not yet registered into m_g.
        unsigned m_eq_qhead = 0;
        unsigned m_deq_qhead = 0;
        // Dependency for each merge/diseq registered into m_g.
        vector<eq_tree::dep_tracker> m_reasons;

    public:
        lex_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm);

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }

        // Trailed lexicographic-obligation insertion.
        void add_lex(expr_ref_vector const& lhs, expr_ref_vector const& rhs, bool strict, eq_tree::dep_tracker dep = nullptr) {
            m_lexs.push_back(str_lex(lhs, rhs, strict, dep));
            m_trail.push(push_back_trail<str_lex>(m_lexs));
        }

        vector<str_lex> const& lexs() const { return m_lexs; }

        // Overwrite entry idx's (lhs,rhs) pair. Trailed.
        void set_sides(unsigned idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs);

        // Trailed removal of the obligation at `idx` (discharged: proved
        // to hold, so no longer pending).
        void remove(unsigned idx) {
            m_trail.push(vector_erase_trail<str_lex>(m_lexs, idx));
            m_lexs.erase(m_lexs.begin() + idx);
        }

        // Apply a broadcast substitution to every pending obligation.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override;
        bool is_satisfied() const override { return m_lexs.empty(); }
        std::ostream& display(std::ostream& out) const override;

        // Keep m_g's scope stack in lockstep with the shared trail.
        void push() override { m_g.push(); }
        void pop() override { m_g.pop(1); }

        // Deterministic simplification pass over all pending obligations.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);

        // Detect cycles among pending obligations after collapsing equal
        // sides through the egraph. A strict cycle is a conflict; an
        // all-non-strict cycle is converted into equations.
        bool detect_cycles(bool& conflict, eq_tree::dep_tracker& conflict_dep, eq_facet& eqf, deq_facet& deqf);

    private:
        // Register newly seen active equations and disequations into m_g.
        bool sync_egraph(eq_facet& eqf, deq_facet& deqf);
    };

    // Deterministic propagation plugin wrapping lex_facet::simplify.
    class lex_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        lex_propagation(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "lex-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-lex-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
