/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ncontains_facet.h

Abstract:

    Negative `str.contains` facet ("Phase 6" of the modular plugin-based
    search tree design, following `stx::` in util/stx_search_tree.h, the
    `eq_facet`/`deq_facet` module (ast/seq/seq_eq_facet.h), and
    `arith_facet` (smt/seq_arith_facet.h)).

    Nielsen (seq_nielsen.h/.cpp) has no support for `str.contains` at all:
    positive `str.contains(h,n)` reduces to an `eq_facet` equation
    `h = x.n.y` for fresh existential Skolems `x`, `y` (not modeled by this
    facet - the caller/preprocessing layer is responsible for that
    reduction, exactly as it is for theory_seq today); only the *negative*
    form `not contains(h,n)` needs a dedicated facet, since it is a
    universal ("no factorization of h contains n"), not a language
    complement the way negating str.in_re is (see z3papers/nseq/
    facet-ncontains.md section 2).

    Design, drawn primarily from theory_seq's existing negative-containment
    machinery (theory_seq.h/.cpp's `class nc`/`m_ncs`/`solve_nc`/
    `unroll_not_contains`) per facet-ncontains.md:

      - `ncontains_facet` owns `vector<str_ncontains>`, each a pending
        `haystack` / `needle` obligation, flattened into `expr_ref_vector`s
        exactly like eq_facet/deq_facet's equations (shared helpers:
        `seq::flatten`, `seq::expr_ref_vector`, `seq::subst_in`) so that a
        substitution chosen by `word_eq_split` keeps every obligation's
        haystack/needle in sync via `subst_sink_i::apply_subst` (this is
        the fix for the nseq monotonicity-soundness gap documented in
        research/docs/nseq-issues/02-soundness-contains-monotonicity.md:
        an obligation is *re-derived* against the current representative
        of `h`, never frozen at creation time - see facet-ncontains.md
        section 4).

      - `ncontains_propagation` (propagation_plugin_i) implements both the
        length-gate check of facet-ncontains.md section 3.3 (given
        `arith_facet`'s incremental backend, ask whether `len(h) < len(n)`
        is already implied - obligation vacuously satisfied, discharge it)
        and, as deterministic propagation rather than a nondeterministic
        split, the recursive prefix-unrolling occurrence search of
        section 3.4: at the haystack's current leading position, either
        the needle's tokens are already resolved distinct from the
        haystack's (safe, unconditional progress - strip the haystack's
        leading token and recurse with no branching), or they resolve to
        a full match (the needle DOES occur - a direct conflict for this
        `not contains` obligation), or the comparison is undecided
        because some token is an unresolved variable (left pending until
        a substitution narrows it, exactly like deq_facet's own
        documented incompleteness). This also detects the trivial
        conflict case `needle = epsilon` (an empty needle is always
        contained, so `not contains(h, "")` is immediately
        unsatisfiable).

    Scope note / simplifications relative to the full design:
      - the ground-needle regex-rewrite alternative reduction of
        facet-ncontains.md section 3.5 (rewriting `not contains(h,n)` to
        a `mem_facet` non-membership `h not-in .*n.*` when `n` is a
        literal string) is NOT implemented in this pass - `mem_facet`'s
        regex-complement construction is left as a documented future
        integration point; the deterministic prefix-unrolling propagation
        (section 3.4) alone is sound and complete for the token-list
        representation this port already uses, just potentially more
        expensive than the regex reduction would be for a long constant
        needle.
      - the termination argument for the prefix-unrolling loop relies on
        the token lists being finite (word equations are already
        required to terminate via eq_facet's own machinery): each step
        strictly shortens the haystack's token list by exactly one
        token, so the loop is bounded by the haystack's initial token
        count - no separate `arith_facet` upper-bound query (section 3.6)
        is needed for termination in this concrete/token-list
        representation (as opposed to an open-ended symbolic length).

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

    // One pending negative-containment obligation: `m_needle` does not
    // occur as an infix of `m_haystack`, represented (like eq_facet's
    // equations) as flattened token lists so that eq_facet substitutions
    // keep it in sync via subst_sink_i.
    struct str_ncontains {
        expr_ref_vector m_haystack;
        expr_ref_vector m_needle;
        eq_tree::dep_tracker m_dep;
        str_ncontains(expr_ref_vector const& h, expr_ref_vector const& n, eq_tree::dep_tracker dep = nullptr) :
            m_haystack(h), m_needle(n), m_dep(dep) {}
        bool operator<(str_ncontains const& other) const;
        bool operator==(str_ncontains const& other) const;
    };

    /**
     * Facet holding a set of pending negative str.contains obligations.
     * See module comment for the propagation responsibilities.
     */
    class ncontains_facet : public stx::facet_i, public subst_sink_i {
        ast_manager& m;
        seq_util&    u;
        eq_tree::dep_manager_t& m_dm;
        vector<str_ncontains> m_ncs;

    public:
        ncontains_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        // Non-trailed: root construction only.
        void add_ncontains(expr_ref_vector const& h, expr_ref_vector const& n, eq_tree::dep_tracker dep = nullptr) {
            m_ncs.push_back(str_ncontains(h, n, dep));
        }
        void add_ncontains(expr* haystack, expr* needle, eq_tree::dep_tracker dep = nullptr) {
            expr_ref_vector hts(m), nts(m);
            flatten(u, haystack, hts);
            flatten(u, needle, nts);
            add_ncontains(hts, nts, dep);
        }

        vector<str_ncontains> const& ncontains() const { return m_ncs; }

        // Drop `idx`'s obligation entirely (discharged/proved). Trailed.
        void remove(unsigned idx);

        // Drop `idx`'s obligation and push a fresh one whose haystack is
        // `new_haystack` (used by ncontains_propagation's deterministic
        // prefix-unrolling: strip one leading haystack token, keep the
        // same needle). Trailed.
        void replace_with_tail(unsigned idx, expr_ref_vector const& new_haystack);

        // Broadcast substitution from eq_facet's Nielsen split - keeps
        // every obligation's haystack/needle in sync with the shared
        // variable pool (the monotonicity-soundness fix, see module
        // comment). The touched obligation's dependency is joined with
        // `subst_dep`, also trailed.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // -- stx::facet_i --
        stx::facet_i* clone(trail_stack& trail) const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_ncs.empty(); }
        std::ostream& display(std::ostream& out) const override;
    };

    // Length-gate propagation (facet-ncontains.md section 3.3), plus the
    // recursive prefix-unrolling occurrence search (facet-ncontains.md
    // section 3.4) - implemented here as *deterministic* propagation
    // rather than as a nondeterministic split, since each step either
    // strictly shortens the haystack's token list (pure progress, no
    // branching) or immediately decides the obligation (conflict/
    // discharge); branching is only needed when the current leading
    // token pairing is genuinely undecided (an unresolved variable is
    // involved), and in that case the obligation is simply left pending
    // until a substitution (broadcast via apply_subst, see facet-
    // ncontains.md section 4) resolves it enough for propagation to
    // proceed - mirroring deq_facet's own "no branching of its own"
    // design (facet-eq-deq.md section 2.5).
    class ncontains_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        stx::facet_id m_ncontains_id;
        stx::facet_id m_arith_id;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        ncontains_propagation(ast_manager& m, seq_util& u, arith_util& a, stx::facet_id ncontains_id, stx::facet_id arith_id) :
            m(m), u(u), a(a), m_ncontains_id(ncontains_id), m_arith_id(arith_id) {}
        char const* name() const override { return "ncontains-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("ncontains-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
