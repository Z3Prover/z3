/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.h

Abstract:

    Sequence power operator (`s^n`, `seq.power`) facet, following `stx::`
    in util/stx_search_tree.h and the `eq_facet`/`arith_facet` modules
    (ast/seq/seq_eq_facet.h, smt/seq_solver_facet.h).

    Design, ported from theory_seq's existing power-operator machinery
    (`theory_seq.h/.cpp`'s `is_power`/`add_power_axiom`/
    `add_power_unfold_axiom`, `seq_axioms.cpp`'s `axioms::power_axiom`/
    `axioms::power_unfold_axiom`) into the modular plugin architecture:

      - `power_facet` owns `vector<str_power>`, each a pending obligation
        `e = s^n` (the power term `e`, its base `s`, and its exponent
        `n`), exactly mirroring `theory_seq`'s per-term bookkeeping (there
        it is driven by `relevant_eh`/`deque_axiom` on `is_power` terms;
        here the obligation is registered explicitly, e.g. by a
        preprocessing/axiomatization layer that spots `seq.power` terms in
        the input, per z3papers/nseq/string-function-coverage.md section
        2's "reduce to existing facets before the search tree ever sees
        them" pattern - except unlike section 2's *purely* Skolemizable
        functions, `s^n` genuinely needs live search-tree participation
        when `n` is symbolic, since the unfolding depth is not fixed in
        advance).

      - `power_propagation` (propagation_plugin_i) implements the
        deterministic part:
          * if `n` is a resolved numeral `j` (`arith_util::is_numeral`),
            the obligation is fully precise and can be discharged exactly
            as `theory_seq`'s "known exponent" branch of
            `power_unfold_axiom` does: for `j <= 0`, add the equation
            `e = epsilon` to `eq_facet`; for `j >= 1`, add the equation
            `e = s ++ .. ++ s` (`j` copies) to `eq_facet`. Either way the
            power obligation itself is then fully discharged (removed) -
            `eq_facet`'s own Nielsen machinery takes it from there.
          * if `n` is symbolic, the *length* consequences of
            `axioms::power_axiom` are asserted into `arith_facet` as
            arithmetic-only clauses (no sequence equality is needed, only
            `str.len`): `n>=1 \/ len(e)=0`, `len(s)!=0 \/ len(e)=0`,
            `~(n>=1) \/ len(e)=n*len(s)`, and
            `~(n>=1) \/ len(s)=0 \/ n<=len(e)`. These are sound
            *under-approximations* of the full (sequence-level) axiom -
            `len(e)=0` stands in for the imprecise-but-sufficient
            "e=epsilon" antecedent/consequent, exactly as `arith_facet`'s
            own module comment documents for its length-only design - and
            are asserted at most once per obligation (idempotency is
            `arith_facet::add_constraint`'s own responsibility, mirroring
            `arith_propagation`).

      - `power_split` (split_plugin_i) implements the nondeterministic
        completeness driver for symbolic exponents, mirroring
        `theory_seq`'s `add_power_unfold_axiom`'s per-`k` case split
        (there driven by `propagate_length_limit`/`should_research`'s
        unfolding-depth escalation loop): for a still-pending obligation
        with a symbolic `n`, branch over `n <= 0` (unify `e = epsilon`)
        and `n = 1, 2, .., bound` (unify `e` with `j` concatenated copies
        of `s` and record `n = j` as an arithmetic fact), up to
        `power_facet::max_unfold()` (a fixed per-facet bound rather than
        `theory_seq`'s dynamically-escalating `m_max_unfolding_depth` -
        the iterative deepening / "should_research" escalation loop is
        left as a documented future integration point, exactly as
        `ncontains_facet`'s own module comment defers the regex-rewrite
        alternative reduction).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    // One pending power obligation `m_e = m_s ^ m_n`.
    struct str_power {
        expr_ref             m_e;
        expr_ref             m_s;
        expr_ref             m_n;
        eq_tree::dep_tracker  m_dep;
        // Set once this obligation's symbolic-exponent length axioms
        // (power_propagation) have been asserted into arith_facet, so
        // they are only ever added once (mirrors arith_propagation's own
        // "changed only if new" idiom, but tracked explicitly here since
        // the four clauses must be added atomically as a group).
        bool                 m_axiomatized = false;

        // Set once `power_fine_wilf` has fired its (non-progress,
        // arith-only) "small overlap" case-1 branch for this obligation,
        // so that branch is not offered again for the same obligation
        // every round (a coarser but sound substitute for the c3 branch's
        // per-(lhs,rhs,direction) `fw_applied` key: since case-1 makes no
        // string-side change at all, without *some* guard the identical
        // split would be re-offered forever). Does not block
        // power_fine_wilf's other (progress) cases 2/3, nor any other
        // plugin, from still acting on this same obligation.
        bool                 m_fw_marked = false;

        str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
            m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
    };

    /**
     * Facet holding a set of pending `s^n` obligations. See module
     * comment for the propagation/split responsibilities.
     */
    class power_facet : public stx::facet_i {
        ast_manager&    m;
        seq_util&       u;
        arith_util&     a;
        eq_tree::dep_manager_t& m_dm;
        vector<str_power> m_pows;
        unsigned        m_max_unfold = 5; // bound on power_split's case-split unfolding, see module comment

    public:
        power_facet(trail_stack& trail, ast_manager& m, seq_util& u, arith_util& a, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), a(a), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        arith_util& get_arith_util() const { return a; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }

        unsigned max_unfold() const { return m_max_unfold; }
        void set_max_unfold(unsigned k) { m_max_unfold = k; }

        // Trailed: for adding a power obligation (root construction or
        // mid-search alike - all constraint additions are trailed, no
        // exception). Undo just pops the pushed element.
        void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
            m_pows.push_back(str_power(m, e, s, n, dep));
            m_trail.push(push_back_trail<str_power>(m_pows));
        }
        // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
        // otherwise. Convenience wrapper for callers scanning terms.
        bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
            expr* s = nullptr, *n = nullptr;
            if (!u.str.is_power(e, s, n))
                return false;
            add_power(e, s, n, dep);
            return true;
        }

        vector<str_power> const& powers() const { return m_pows; }

        // Locate the (unique, since power terms are hash-consed) pending
        // obligation whose power term is `e`, if any. Used by plugins
        // (power_fine_wilf) that need to recognize a `seq.power` token
        // appearing inside an eq_facet equation's token list - since
        // eq_facet::get_concat_units() treats `seq.power` terms as opaque single
        // tokens (it does not decompose them), this linear scan over the
        // (typically small) pending-obligation set is how a plugin
        // bridges "this token is a power term" back to "here is its
        // base/exponent/dependency".
        bool find_power(expr* e, unsigned& idx) const {
            for (unsigned i = 0; i < m_pows.size(); ++i)
                if (m_pows[i].m_e.get() == e) {
                    idx = i;
                    return true;
                }
            return false;
        }

        // Drop `idx`'s obligation entirely (fully discharged into
        // eq_facet). Trailed.
        void remove(unsigned idx);

        // Mark `idx`'s obligation as having had its length axioms
        // asserted (so power_propagation does not re-assert them every
        // round). Trailed.
        void set_axiomatized(unsigned idx);

        // Mark `idx`'s obligation as having had power_fine_wilf's case-1
        // ("small overlap") branch already offered (see str_power's
        // m_fw_marked comment). Trailed.
        void set_fw_marked(unsigned idx);

        // -- stx::facet_i --
        stx::facet_i* clone(trail_stack& trail) const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_pows.empty(); }
        std::ostream& display(std::ostream& out) const override;
    };

    // Deterministic propagation: known-exponent obligations are fully
    // unfolded into an eq_facet equation and discharged; symbolic-exponent
    // obligations get their length-only axiom clauses asserted into
    // arith_facet (once). See module comment.
    class power_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        power_propagation(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("power-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Bounded case-split completeness driver for symbolic exponents: see
    // module comment.
    class power_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_pow_index;
            unsigned       m_next_j; // next exponent to try (1..bound)
            unsigned       m_bound;
            eq_tree::dep_tracker m_dep;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      unsigned pow_index, unsigned bound, eq_tree::dep_tracker dep,
                      ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n),
                m_pow_index(pow_index), m_next_j(1), m_bound(bound), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_split(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Fine & Wilf periodicity rule, ported from the c3 branch's
    // seq_nielsen_modifiers.cpp `apply_fine_wilf` (see z3papers/nseq's
    // facet-eq-deq.md design-doc comments on Fine & Wilf for the
    // underlying combinatorics-on-words argument). Only the fully
    // symbolic path is implemented (all three cases below, which are
    // jointly - not individually - sound); the ground-string
    // enumeration fast path that c3 uses as a pure optimization ahead of
    // the symbolic path is deliberately not ported (documented
    // completeness/perf gap, not a soundness one: the symbolic path
    // alone already covers every ground instance, just less directly).
    //
    // Trigger pattern: some eq_facet equation has, at its head, a power
    // token `U^n` on one side (recognized via power_facet::find_power on
    // the token, since eq_facet::get_concat_units() never decomposes `seq.power`
    // terms - they remain single opaque tokens in the equation's token
    // list) and, on the other side, a run of zero-or-more non-power
    // tokens `Y` immediately followed by a *different* power token
    // `W^m` (same-base overlaps are already handled by ordinary
    // propagation/word_eq_split, so this rule only fires when the two
    // bases are syntactically distinct terms - it does not attempt to
    // prove/refute base equality itself).
    //
    // Given `Ly = len(Y)`, `len_upow = len(U^n) = n*len(U)`,
    // `len_wpow = len(W^m) = m*len(W)`, and threshold
    // `T = len(U) + len(W)` (a sound weakening of the exact
    // Fine & Wilf bound `len(U)+len(W)-gcd(len(U),len(W))`, avoiding a
    // non-linear gcd term - see design doc), the three branches are:
    //
    //   Case 1 (small overlap; arith-only, no string-side progress):
    //     side constraint `len_upow - Ly < T \/ len_wpow < T`. Guarded by
    //     `str_power::m_fw_marked` so it is only ever offered once per
    //     obligation (it makes no string-side change, so without a guard
    //     it would be re-offered forever).
    //   Case 2 (progress; eliminates `U^n`): fresh `R1, R2` with
    //     `U^n = Y.R1`, `W^m = R1.R2`, `V = R2.Z`, plus
    //     `Ly + |R1| = len_upow`, `|R1| >= T`, `|R1| + |R2| = len_wpow`.
    //   Case 3 (progress; eliminates `W^m`): fresh `S1, S2` with
    //     `U^n = S1.S2`, `S1 = Y.W^m`, `Z = S2.V`, plus
    //     `|S1| = Ly + len_wpow`, `len_wpow >= T`, `|S2| >= 1`,
    //     `|S1| + |S2| = len_upow`.
    //
    // All three are generated together as sibling branches (jointly
    // sound; individually each is only a sound *strengthening*, not an
    // equivalence, of the disjunction the three together represent).
    class power_fine_wilf : public eq_tree::split_plugin_i {
    public:
        // Trigger-site description, computed once by split() and reused
        // by the iterator for the remaining (case 2 / case 3) branches
        // after case 1 (if offered) is the first, immediately
        // materialized branch.
        struct trigger {
            unsigned    m_eq_idx;
            bool        m_pow_on_lhs;   // U^n is eq.lhs[0] (true) or eq.rhs[0] (false)
            unsigned    m_pow_idx;      // power_facet index of U^n
            unsigned    m_other_pow_idx; // power_facet index of W^m
            unsigned    m_y_len;        // number of non-power tokens making up Y
            eq_tree::dep_tracker m_dep;
        };

    private:
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            trigger        m_t;
            unsigned       m_next_case; // 2, then 3, then done
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      trigger const& t, unsigned next_case, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n),
                m_t(t), m_next_case(next_case), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_fine_wilf(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-fine-wilf"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-fine-wilf num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Same-base power-vs-power exponent comparison, ported from the c3
    // branch's seq_nielsen_modifiers.cpp `apply_num_cmp`: when some
    // eq_facet equation has, at the same directional end (both heads or
    // both tails) of each side, a power token with the *same* base but a
    // different registered obligation (i.e. `U^n` and `U^m` for the same
    // `U`, appearing as distinct tokens - this can only happen before
    // `power_propagation`'s known-exponent unfold or `word_eq_split`'s
    // ordinary token matching has fired, e.g. right after two such
    // obligations are first registered against the same equation), the
    // relative order of `n` and `m` is not yet determined and must be
    // case-split on directly (arith-only, no string-side progress in
    // either branch - unlike power_fine_wilf, this rule's whole point is
    // to let arith_facet resolve the comparison, after which ordinary
    // simplification/propagation can cancel the common `U^min(n,m)`
    // prefix/suffix):
    //
    //   Branch 1: n < m   (side constraint `m >= n + 1`)
    //   Branch 2: m <= n  (side constraint `n >= m`)
    //
    // Mirrors c3's two `mk_edge`/`add_side_constraint` branches exactly
    // (both marked `set_arith_split()` there, i.e. exempt from the
    // sibling loop-cut/unsat-cache since they differ only in an
    // arithmetic fact, not in any string-level substitution - c3mv has
    // no equivalent exemption mechanism yet, so both branches are
    // offered as ordinary split alternatives here). Guarded so it is
    // only offered for a given pair of obligations once their exponents
    // are not already resolvable as a constant difference (that case is
    // handled by ordinary equation simplification/propagation once one
    // side is a numeral, per power_propagation's known-exponent branch).
    class power_num_cmp : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            expr_ref       m_n_exp;
            expr_ref       m_m_exp;
            eq_tree::dep_tracker m_dep;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
            bool           m_done = false;
        public:
            iterator(eq_tree::node& n, expr* n_exp, expr* m_exp,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_n_exp(n_exp, m), m_m_exp(m_exp, m), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_num_cmp(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-num-cmp"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-num-cmp num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // General same-base power-vs-token-run exponent comparison, ported
    // from the c3 branch's `apply_split_power_elim`
    // (seq_nielsen_modifiers.cpp), generalizing power_num_cmp: instead of
    // requiring the *other* side's directional end to itself be a
    // registered power obligation with the same base, this rule scans a
    // whole prefix/suffix run of the other side for repeated copies of
    // the power's own base pattern `U` (a `comm_power`-style match:
    // ordinary tokens matching `U`'s flattened token pattern verbatim,
    // plus - only at a pattern boundary - another power token whose base
    // is the *same* pattern, whose whole exponent is absorbed into the
    // running count), accumulating a symbolic "how many copies of U were
    // just consumed" expression `count`. Once some nonzero-length prefix
    // run has been matched this way, the relative order of `count`
    // versus `U^n`'s own exponent `n` is generally undetermined and must
    // be case-split on, exactly like power_num_cmp:
    //
    //   Branch 1: n < count    (side constraint `count >= n + 1`)
    //   Branch 2: count <= n   (side constraint `n >= count`)
    //
    // Both are pure arith_facet side constraints (no string-side
    // progress in either branch, same as power_num_cmp) - after either
    // is asserted, ordinary propagation can cancel the common
    // `U^min(n,count)` prefix/suffix. Guarded so it is only offered when
    // `count` and `n` are not both already-resolved numerals (that case
    // needs no case split).
    class power_split_elim : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            expr_ref       m_pow_exp;
            expr_ref       m_count;
            eq_tree::dep_tracker m_dep;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
            bool           m_done = false;
        public:
            iterator(eq_tree::node& n, expr* pow_exp, expr* count,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_pow_exp(pow_exp, m), m_count(count, m), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_split_elim(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-split-elim"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-split-elim num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Power-vs-variable peel, ported from the c3 branch's
    // seq_nielsen_modifiers.cpp `apply_var_num_unwinding_eq`. Trigger
    // pattern: some eq_facet equation has, at the same directional end
    // (front or back) of its two sides, a power token `U^n` opposite a
    // Nielsen-substitutable variable token `v` (i.e. neither a unit nor
    // a power - per z3papers/nseq's README.md section 5.1.1 token model;
    // computed locally as `!u.str.is_unit(x) && !u.str.is_power(x)`,
    // mirroring word_eq_split's own convention, not via
    // ambient_context_i::is_var/theory_seq::is_var). This is exactly
    // word_eq_split's "one side unit, other side variable" case, except
    // with the unit token replaced by a power token - word_eq_split
    // itself explicitly skips any equation whose head is a power (see
    // its own comment), so this rule is what fills that gap for the
    // power-vs-variable pairing specifically (the power-vs-non-variable
    // pairing, e.g. power-vs-unit or power-vs-different-base-power, is
    // instead power_num_cmp/power_split_elim's territory - a plain
    // "peel one copy" step like this one would be unsound/incomplete
    // there since a non-variable head cannot simply be grown by
    // `v := u.v'`).
    //
    // Two branches (both justified by the equation's own dependency):
    //   1. `n = 0`: replace `U^n` with epsilon (progress). Side
    //      constraint `n = 0` (via `n>=0` and `n<=0`, matching c3's own
    //      two-clause form for this branch specifically - see
    //      `apply_var_num_unwinding_eq`, as opposed to
    //      `apply_const_num_unwinding`'s single `n=0` clause for the
    //      analogous non-variable-head case; c3 is not fully consistent
    //      between the two, but both encode the same fact).
    //   2. `n >= 1`: peel one copy, replacing `U^n` with `U . U^(n-1)`
    //      (a *nested* power token, not a fresh string variable, so
    //      that ordinary propagation/simplification can merge/cancel
    //      adjacent same-base powers exactly as power_split's own
    //      per-`j` unfold does) at the same directional end that `U^n`
    //      originally occupied, and substituting `v := U . v'` for a
    //      fresh `v'` on the other side (the variable's own Nielsen
    //      peel, in lock-step with the power's).
    class power_var_peel : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_eq_idx;
            bool           m_pow_on_lhs;
            bool           m_fwd;
            unsigned       m_pow_idx;
            expr_ref       m_var; // the variable token opposite U^n, captured before any mutation
            eq_tree::dep_tracker m_dep;
            bool           m_done = false;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      unsigned eq_idx, bool pow_on_lhs, bool fwd, unsigned pow_idx, expr* var,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n),
                m_eq_idx(eq_idx), m_pow_on_lhs(pow_on_lhs), m_fwd(fwd), m_pow_idx(pow_idx), m_var(var, m),
                m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_var_peel(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-var-peel"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-var-peel num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Variable-vs-power decomposition, ported from the c3 branch's
    // seq_nielsen_modifiers.cpp `apply_power_split` (facet-eq-deq.md
    // section 2.3). Trigger pattern: some eq_facet equation has, at a
    // directional end (front or back) of one side, a Nielsen-
    // substitutable variable token `v` (neither a unit nor a power),
    // opposite a power token `U^n` at the matching end of the other
    // side, where `U`'s own flattened base is itself made of more than
    // one token pattern instance the rule can decompose against.
    // Unlike `power_var_peel` (which only ever peels a single copy of
    // `U` and keeps the remaining `U^(n-1)` as an opaque nested power),
    // this rule decomposes `U`'s *own* base token pattern at every
    // possible position, and additionally offers a "non-progress"
    // branch where `v` simply extends past the whole power term. Since
    // both rules can fire on the same trigger, and `power_var_peel`'s
    // single-copy peel is strictly the cheaper/more incremental step,
    // this rule is intentionally not merged with it - both are offered
    // by the search driver's own cost-ordering machinery, not gated
    // against each other here.
    //
    // Let `t_0, t_1, ..., t_{k-1}` be `U`'s own flattened base tokens
    // (in the direction `v` faces `U^n`, i.e. reversed if `fwd` is
    // false), and let `n` be `U^n`'s exponent (fresh skolem `m`
    // introduced per *target variable*, not per branch, mirroring c3's
    // `get_or_create_gpower_n_var` cache - see class comment on
    // `m_n_cache`/`m_m_cache` below). One branch is generated per
    // decomposition position `i` in `0..k-1` (skipped when `i>0` and
    // `t_{i-1}` is itself a power token, since that position's `m'`
    // range already covers this one - mirrors c3's own skip guard):
    //   - if `t_i` is a plain (non-power) token:
    //       `v := U^m . t_0 . t_1 . ... . t_{i-1}`,  side constraint `m>=0`
    //   - if `t_i` is itself a power token `w^e` (base `w`, exponent `e`):
    //       `v := U^m . t_0 . ... . t_{i-1} . w^m'`, fresh `m'` per
    //       target variable, side constraints `m>=0`, `0<=m'<=e`
    // plus one final "extend past the power" branch (non-progress,
    // required for completeness - without it, solutions where `v`'s
    // value is strictly longer than `U^n` itself are unreachable):
    //   `v := U^n . v'` for a fresh `v'`, side constraint `len(v')>=0`
    // (all branches, and the fresh skolems' side constraints, are
    // justified by the equation's own dependency).
    class power_var_decompose : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        // Per-target-variable cache of the fresh exponent skolem `m`
        // used for `U^m` (the "how much of U has v already consumed"
        // counter) - mirrors c3's `get_or_create_gpower_n_var`. Keyed
        // by the target variable's ast pointer so repeated re-triggering
        // of this rule on the same variable reuses the same skolem
        // rather than minting an unbounded number of them. Not trailed:
        // like `power_split::m_next_j`, this is a monotonic counter-ish
        // cache owned by the plugin itself (shared across the whole
        // search tree, not per-branch), so leftover entries from an
        // abandoned branch are harmless dead skolems, not a soundness
        // issue.
        obj_map<expr, expr*> m_n_cache;
        obj_map<expr, expr*> m_m_cache;

        expr* get_or_create_n_var(expr* var);
        expr* get_or_create_m_var(expr* var);

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            expr_ref       m_var;
            expr_ref       m_pow_e;      // the U^n token being decomposed
            expr_ref_vector m_base_toks; // U's own flattened base tokens, in the direction v faces U^n
            expr_ref       m_fresh_m;    // U^m skolem exponent (shared across all branches below)
            bool           m_fwd;
            eq_tree::dep_tracker m_dep;
            unsigned       m_pos = 0;    // next decomposition position to offer, or m_base_toks.size() once exhausted
            bool           m_extend_done = false; // whether the final "extend past" branch has been offered
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
            power_var_decompose* m_owner;
        public:
            iterator(eq_tree::node& n,
                      expr* var, expr* pow_e, expr_ref_vector const& base_toks, expr* fresh_m, bool fwd,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a, power_var_decompose* owner) :
                m_n(n), m_var(var, m), m_pow_e(pow_e, m),
                m_base_toks(base_toks), m_fresh_m(fresh_m, m), m_fwd(fwd), m_dep(dep), m(m), u(u), a(a), m_owner(owner) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_var_decompose(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-var-decompose"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-var-decompose num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Generalized power introduction, ported from the c3 branch's
    // seq_nielsen_modifiers.cpp `apply_gpower_intr`/`fire_gpower_intro`
    // (facet-eq-deq.md section 2.3). Trigger pattern ("self-cycle"):
    // some eq_facet equation has, at a directional end (front or back)
    // of one side, a Nielsen-substitutable variable `v`, while the
    // *other* side, scanned from the matching end, consists of a
    // non-empty run of non-variable ("ground") tokens followed by that
    // *same* variable `v` reappearing. (Transitive cycles spanning
    // several equations are not detected - c3 leaves this as a TODO
    // too.)
    //
    // On firing: the ground run is compressed to its minimal repeating
    // period (e.g. `[a,b,a,b]` has period 2, so the power base becomes
    // `[a,b]` rather than the redundant `[a,b,a,b]`); if the compressed
    // period is itself a single power token, it is unwrapped to its own
    // base tokens first (avoiding a nested power-of-power). A fresh
    // exponent skolem `n` is introduced (per target variable, cached -
    // mirrors `power_var_decompose`'s own `get_or_create_n_var`, though
    // this rule keeps a separate cache since its target variables and
    // c3's own `get_or_create_gpower_n_var` cache are shared across both
    // rules there - a minor, harmless divergence: at worst two separate
    // skolems are minted for the same variable across the two rules
    // rather than one shared skolem), giving `base^n`. Exactly as
    // `power_var_decompose`, one branch is generated per decomposition
    // position `i` of the compressed base (skipped when `i>0` and
    // position `i-1` is itself a power token), substituting
    // `v := base^n . t_0 . ... . t_{i-1}` (or, at a power-token
    // position, `v := base^n . t_0 . ... . t_{i-1} . w^m'` with a fresh
    // partial exponent `0<=m'<=inner_exp`), each with side constraint
    // `n>=0` (plus `m'>=0`/`m'<=inner_exp` when used). Unlike
    // `power_var_decompose`, there is no separate "extend past" branch
    // here - the reappearance of `v` itself at the tail of the ground
    // run *is* the completion of the cycle, so the decomposition
    // positions alone are exhaustive (every position up to and
    // including the last one, where `t_{k-1}` is the token immediately
    // preceding `v`'s own reappearance, is covered).
    class power_gpower_intro : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        // See power_var_decompose's own m_n_cache/m_m_cache comment;
        // same idiom, separate cache (see class comment above).
        obj_map<expr, expr*> m_n_cache;
        obj_map<expr, expr*> m_m_cache;

        expr* get_or_create_n_var(expr* var);
        expr* get_or_create_m_var(expr* var);

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            expr_ref       m_var;
            expr_ref       m_pow_e;       // the fresh base^n power token
            expr_ref_vector m_base_toks;  // compressed ground-prefix base tokens, in the direction v faces the cycle
            expr_ref       m_fresh_n;     // base^n skolem exponent (shared across all branches below)
            bool           m_fwd;
            eq_tree::dep_tracker m_dep;
            unsigned       m_pos = 0;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
            power_gpower_intro* m_owner;
        public:
            iterator(eq_tree::node& n,
                      expr* var, expr* pow_e, expr_ref_vector const& base_toks, expr* fresh_n, bool fwd,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a, power_gpower_intro* owner) :
                m_n(n), m_var(var, m), m_pow_e(pow_e, m),
                m_base_toks(base_toks), m_fresh_n(fresh_n, m), m_fwd(fwd), m_dep(dep), m(m), u(u), a(a), m_owner(owner) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_gpower_intro(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-gpower-intro"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-gpower-intro num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

} // namespace seq
