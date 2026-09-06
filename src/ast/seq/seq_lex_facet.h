/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_lex_facet.h

Abstract:

    Lexicographic comparison facet: `str.<` / `str.<=`.

    `theory_nseq::assign_eh` used to handle `str.<`/`str.<=` purely by
    axiomatizing them away (via `m_ax.add_lt_axiom`/`add_le_axiom`, see
    `ast/seq/seq_axioms.cpp`'s `axioms::lt_axiom`/`le_axiom`), which
    reduces `e1 < e2` to a disjunctive clause over freshly Skolemized
    "common prefix / first differing character" existentials
    (`x . unit(c) . y = e1`, `x . unit(d) . z = e2`, `c < d`, or one side
    being a prefix of the other). That is sound but leaves all of the
    actual case analysis to the SAT engine's own case-splitting rather
    than exploiting the token-level machinery `eq_facet`/`deq_facet`
    already provide.

    `lex_facet` instead accumulates pending `(lhs, rhs, is_strict)`
    lexicographic-order obligations directly as token vectors (via
    `get_concat_units`, exactly like `eq_facet`/`deq_facet`), so
    `lex_propagation` can peel off leading tokens that are either two
    directly-comparable character constants (deciding the comparison
    outright, or - if equal - letting the peel continue) or two tokens
    already known equal (any token, not just constants: stripped
    unconditionally, mirroring `deq_facet::simplify`'s own common-prefix
    stripping). This mirrors `theory_seq.cpp`'s own `str.<`/`str.<=`
    axiom shape (`seq_axioms.cpp`'s `lt_axiom`: peel a common prefix `x`,
    then compare the first differing characters `c`/`d`, with the
    remaining `pref12`/`pref21` prefix cases falling out when one side is
    exhausted first) - `lex_facet` is simply the incremental, token-level
    analogue of that same case split, so that constant-heavy comparisons
    (e.g. `"ab" < "ac"`, `"ab" <= x` for concrete `x`) get resolved
    directly instead of only via SAT-level case splitting.

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
      - Otherwise (leading tokens are not two comparable constants, e.g.
        at least one is a variable): the obligation is left pending
        (sound but incomplete, exactly like `deq_facet`'s own "stuck"
        case) for a future round, e.g. once further substitution
        resolves the leading tokens further.

    `m_qhead` is *not* used the way `req_facet` uses it (entries here are
    revisited every round, since - unlike `req_facet`'s ground bisimulation
    calls - stripping/discharging can make progress once other facets'
    substitutions change a pending entry's leading tokens); it is instead
    used purely to bound the "already fully stripped, nothing more to do
    this round" fast path, exactly like `eq_facet`'s own per-entry
    residual tracking. (Present per the general facet convention even
    though this facet's obligations are not substituted into by
    `eq_facet`'s split machinery today - see module note in
    `lex_propagation::propagate` - so that adding such wiring later needs
    no facet-shape change.)

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    // One pending lexicographic-order obligation: `lhs < rhs` (m_strict)
    // or `lhs <= rhs` (!m_strict), where `lhs`/`rhs` are token vectors
    // (see get_concat_units) rather than raw sequence terms.
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

    public:
        lex_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }

        // Trailed: for adding a lexicographic-comparison obligation
        // (root construction or mid-search alike - all constraint
        // additions are trailed, no exception).
        void add_lex(expr_ref_vector const& lhs, expr_ref_vector const& rhs, bool strict, eq_tree::dep_tracker dep = nullptr) {
            m_lexs.push_back(str_lex(lhs, rhs, strict, dep));
            m_trail.push(push_back_trail<str_lex>(m_lexs));
        }

        vector<str_lex> const& lexs() const { return m_lexs; }

        // Overwrite entry idx's (lhs,rhs) pair (e.g. after stripping a
        // common prefix). Trailed.
        void set_sides(unsigned idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs);

        // Trailed removal of the obligation at `idx` (discharged: proved
        // to hold, so no longer pending).
        void remove(unsigned idx) {
            m_trail.push(vector_erase_trail<str_lex>(m_lexs, idx));
            m_lexs.erase(m_lexs.begin() + idx);
        }

        // Apply a substitution `var := repl` (chosen elsewhere, by
        // eq_facet's split plugin) to every pending obligation - kept
        // for symmetry with deq_facet (see subst_sink_i); lex_facet is
        // registered as a subst_sink_i so that variables shared with
        // eq_facet's equations get substituted here too, letting stuck
        // obligations become resolvable once their leading tokens turn
        // into constants.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override;
        bool is_satisfied() const override { return m_lexs.empty(); }
        std::ostream& display(std::ostream& out) const override;

        // Deterministic simplification pass: strip common leading
        // (already-equal) tokens, then discharge/conflict once one side
        // is exhausted or the leading tokens are distinct comparable
        // constants. On conflict, sets `conflict_dep` to the culprit
        // obligation's dependency. Trailed.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);
    };

    // Deterministic propagation plugin wrapping lex_facet::simplify.
    // Reads its own facet id via the ambient context's lex_id().
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
        void collect_statistics(::statistics& st) const override { st.update("lex-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
