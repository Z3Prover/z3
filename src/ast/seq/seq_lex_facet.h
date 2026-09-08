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

    `m_eq_qhead`/`m_deq_qhead` track which prefix of `eq_facet::equations()`/
    `deq_facet::disequations()` has already been registered into this
    facet's own incremental `euf::egraph` (`m_g`, pushed/popped in
    lockstep with the shared trail's scopes via `push()`/`pop()`), so
    `detect_cycles` re-registers only the genuinely new active entries on
    each call instead of rebuilding `m_g` from scratch every time -
    mirroring `req_facet`'s own `m_qhead` convention (see
    `seq_req_facet.h`). If nothing new has been asserted since the last
    call (no new active equations/disequations, and no pending lex
    obligations at all), `detect_cycles` is a no-op.

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

        // Incremental egraph, owned by this facet (see module comment's
        // former TODO, now implemented): registers eq_facet's/deq_facet's
        // equations/disequations plus every pending lex obligation's
        // token-concat terms, so that two obligations whose sides are
        // only *equal* (not syntactically identical) collapse onto the
        // same digraph node in detect_cycles. Pushed/popped in lockstep
        // with the shared trail via push()/pop() below (one scope per
        // call, mirroring the DFS driver's own one-scope-at-a-time
        // discipline - see stx_search_tree.h's scoped_push).
        euf::egraph m_g;
        // Index of the first eq_facet::equations()/deq_facet::disequations()
        // entry not yet registered into m_g. Trailed (value_trail),
        // advanced forward only by sync_egraph() below - mirrors
        // req_facet::m_qhead's convention (see seq_req_facet.h).
        unsigned m_eq_qhead = 0;
        unsigned m_deq_qhead = 0;
        // Dependency for each merge/diseq registered into m_g, indexed by
        // the packed `void*` reason (to_ptr/from_ptr in seq_lex_facet.cpp)
        // - append-only, trailed via push_back_trail, so indices handed
        // out to earlier egraph justifications stay valid across pops.
        vector<eq_tree::dep_tracker> m_reasons;

    public:
        lex_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm);

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

        // Scope-boundary hooks: keep m_g's own scope stack (independent
        // of eq_facet/deq_facet's own trailing) exactly in lockstep with
        // the shared trail, one push()/pop(1) per call - see
        // stx_search_tree.h's scoped_push, which calls every installed
        // facet's push()/pop() once per DFS branch (de)scent.
        void push() override { m_g.push(); }
        void pop() override { m_g.pop(1); }

        // Deterministic simplification pass: strip common leading
        // (already-equal) tokens, then discharge/conflict once one side
        // is exhausted or the leading tokens are distinct comparable
        // constants. On conflict, sets `conflict_dep` to the culprit
        // obligation's dependency. Trailed.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);

        // Cycle detection over single-variable obligations: builds a
        // reachability graph whose nodes are the variables appearing as
        // a lone token on either side of a still-pending obligation
        // (lhs/rhs each exactly one token, i.e. `x < y` / `x <= y` with
        // `x`,`y` not yet resolved into longer token sequences), and
        // whose edges are those obligations (strict or not). A cycle
        // containing at least one strict edge is a conflict (no total
        // order can satisfy `x <= ... <= x < ...`). A cycle made up
        // entirely of non-strict edges instead forces every variable on
        // the cycle to be pairwise equal: those obligations are removed
        // and re-asserted as equations on `eqf` instead (with the
        // dependency being the join of every edge on the cycle), which
        // is strictly more informative than leaving them as `<=`
        // obligations here. Returns true if it changed the facet's
        // pending set (either by discharging a would-be-equality cycle
        // into equations, or by finding a conflict). Trailed.
        //
        // Uses this facet's own incremental `m_g` (see class comment
        // above) to register only the equations (`eqf`)/disequations
        // (`deqf`) added since `m_eq_qhead`/`m_deq_qhead` (advancing
        // those qheads forward, trailed), together with the token
        // sequences appearing in this facet's pending obligations, so
        // that two obligations whose sides are only *equal* (not
        // syntactically identical) collapse onto the same digraph node
        // (identified by the egraph root's expr - "nodes labeled by ids
        // for the roots of equivalence class"). If registering the
        // equations/disequations alone already yields a conflict (e.g.
        // `deqf` asserts `s1 != s2` but `eqf`'s equations force
        // `s1 == s2`), that conflict is reported directly, with
        // `conflict_dep` extracted via the egraph's justification
        // machinery (`explain`) rather than lex_facet's own dependencies.
        // Only active() equations/disequations/obligations are ever
        // registered or scanned. If there is nothing new to register
        // (no new active equations/disequations since the qheads, and
        // no pending lex obligations at all), this is a no-op and
        // returns false without touching `m_g`.
        bool detect_cycles(bool& conflict, eq_tree::dep_tracker& conflict_dep, eq_facet& eqf, deq_facet& deqf);

    private:
        // Registers every not-yet-seen active equation/disequation
        // (advancing m_eq_qhead/m_deq_qhead) into m_g. Returns true if
        // anything new was registered (informs detect_cycles' no-op
        // check together with whether any lex obligation is pending).
        bool sync_egraph(eq_facet& eqf, deq_facet& deqf);
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
        void collect_statistics(::statistics& st) const override { st.update("seq-lex-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
