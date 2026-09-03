/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.h

Abstract:

    Sequence power operator (`s^n`, `seq.power`) facet, following `stx::`
    in util/stx_search_tree.h and the `eq_facet`/`arith_facet` modules
    (ast/seq/seq_eq_facet.h, smt/seq_arith_facet.h).

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

        // Non-trailed: root construction only.
        void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
            m_pows.push_back(str_power(m, e, s, n, dep));
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
        // eq_facet::flatten() treats `seq.power` terms as opaque single
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
    };

    // Deterministic propagation: known-exponent obligations are fully
    // unfolded into an eq_facet equation and discharged; symbolic-exponent
    // obligations get their length-only axiom clauses asserted into
    // arith_facet (once). See module comment.
    class power_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        stx::facet_id m_pow_id;
        stx::facet_id m_eq_id;
        stx::facet_id m_arith_id;
    public:
        power_propagation(ast_manager& m, seq_util& u, arith_util& a, stx::facet_id pow_id, stx::facet_id eq_id, stx::facet_id arith_id) :
            m(m), u(u), a(a), m_pow_id(pow_id), m_eq_id(eq_id), m_arith_id(arith_id) {}
        char const* name() const override { return "power-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

    // Bounded case-split completeness driver for symbolic exponents: see
    // module comment.
    class power_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        stx::facet_id m_pow_id;
        stx::facet_id m_eq_id;
        stx::facet_id m_arith_id;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_pow_id;
            stx::facet_id  m_eq_id;
            stx::facet_id  m_arith_id;
            unsigned       m_pow_index;
            unsigned       m_next_j; // next exponent to try (1..bound)
            unsigned       m_bound;
            eq_tree::dep_tracker m_dep;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n, stx::facet_id pow_id, stx::facet_id eq_id, stx::facet_id arith_id,
                      unsigned pow_index, unsigned bound, eq_tree::dep_tracker dep,
                      ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_pow_id(pow_id), m_eq_id(eq_id), m_arith_id(arith_id),
                m_pow_index(pow_index), m_next_j(1), m_bound(bound), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_split(ast_manager& m, seq_util& u, arith_util& a, stx::facet_id pow_id, stx::facet_id eq_id, stx::facet_id arith_id) :
            m(m), u(u), a(a), m_pow_id(pow_id), m_eq_id(eq_id), m_arith_id(arith_id) {}
        char const* name() const override { return "power-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
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
    // the token, since eq_facet::flatten() never decomposes `seq.power`
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
        stx::facet_id m_pow_id;
        stx::facet_id m_eq_id;
        stx::facet_id m_arith_id;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_pow_id;
            stx::facet_id  m_eq_id;
            stx::facet_id  m_arith_id;
            trigger        m_t;
            unsigned       m_next_case; // 2, then 3, then done
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n, stx::facet_id pow_id, stx::facet_id eq_id, stx::facet_id arith_id,
                      trigger const& t, unsigned next_case, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_pow_id(pow_id), m_eq_id(eq_id), m_arith_id(arith_id),
                m_t(t), m_next_case(next_case), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_fine_wilf(ast_manager& m, seq_util& u, arith_util& a, stx::facet_id pow_id, stx::facet_id eq_id, stx::facet_id arith_id) :
            m(m), u(u), a(a), m_pow_id(pow_id), m_eq_id(eq_id), m_arith_id(arith_id) {}
        char const* name() const override { return "power-fine-wilf"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

} // namespace seq
