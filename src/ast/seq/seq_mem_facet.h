/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.h

Abstract:

    Positive regular-expression membership facet ("Phase 5" of the modular
    plugin-based search tree design, following `stx::` in
    util/stx_search_tree.h and the `eq_facet`/`deq_facet` and `arith_facet`
    modules).

    A `str_mem` constrains one sequence term against a `seq::view`: either a
    plain membership `<state,null>` meaning the whole term is in the language
    of `state`, or a reach view `<state,target>` meaning the term drives the
    derivative automaton from `state` to `target`.

    This port deliberately keeps the facet small and delegates regex-specific
    search to already-existing components:
      - deterministic discharge / conflict checks use `seq::accepts`,
        `seq::is_dead`, and `seq::live_states`;
      - multi-view landing splits are delegated to `seq_monadic`;
      - substitutions chosen by `word_eq_split` are broadcast here through
        `subst_sink_i`, so pending memberships stay synchronized with the
        shared variable pool.

    Scope note / simplifications relative to the full design:
      - regex factorization (§4.2 of facet-membership.md) is NOT implemented
        in this pass;
      - the c3 branch's `apply_regex_var_split` (a per-membership
        Nielsen-style variable split, `x -> epsilon` / `x -> c.x'`) is not
        ported here: monadic landing (`mem_monadic_split`, driven by
        `seq_monadic`) subsumes it as the sole membership-side splitting
        rule, so no standalone `mem_var_split` class exists in this port;
      - monadic landing is implemented for the conjunction of memberships
        currently present in `mem_facet`; it narrows views reported by
        `seq_monadic::iterate()` and leaves exact witness materialization to
        `seq_monadic` itself.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_view.h"
#include "ast/seq/seq_regex_live.h"
#include "ast/seq/seq_monadic.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    struct str_mem {
        expr_ref_vector      m_str;
        view                 m_view;
        eq_tree::dep_tracker m_dep = nullptr;

        str_mem(ast_manager& m, expr* s, view const& v, eq_tree::dep_tracker dep = nullptr) :
            m_str(m), m_view(v), m_dep(dep) {
            seq_util(m).str.get_concat_units(s, m_str);
        }
        str_mem(ast_manager& m, expr_ref_vector const& ts, view const& v, eq_tree::dep_tracker dep = nullptr) :
            m_str(ts), m_view(v), m_dep(dep) {}

        bool is_plain() const { return m_view.is_membership(); }
        bool is_view() const { return m_view.is_reach(); }

        bool operator<(str_mem const& other) const {
            int c = cmp_tokens(m_str, other.m_str);
            if (c != 0)
                return c < 0;
            return m_view.key() < other.m_view.key();
        }
        bool operator==(str_mem const& other) const {
            return cmp_tokens(m_str, other.m_str) == 0 && m_view.key() == other.m_view.key();
        }
    };

    class mem_facet : public stx::facet_i, public subst_sink_i {
        ast_manager&      m;
        seq_util&         u;
        eq_tree::dep_manager_t& m_dm;
        vector<str_mem>   m_mems;
        // Set once mem_monadic_split has certified that every remaining
        // membership constraint has been narrowed to a variable-only
        // view (x_i in view_i) whose intersection seq_monadic verified
        // to be non-empty. apply_subst() (a structural change to some
        // membership's string) clears this again, since the narrowed
        // views no longer necessarily reflect the (now different) set
        // of constraints - mem_monadic_split must re-certify.
        bool              m_is_satisfied = false;

    public:
        mem_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }
        vector<str_mem> const& memberships() const { return m_mems; }

        void add(str_mem const& sm);
        void narrow(unsigned idx, view const& new_view);
        void remove(unsigned idx);
        // Replace `idx`'s own string term wholesale (as opposed to
        // `apply_subst`'s global variable-keyed rewrite): used by
        // plugins that peel/rewrite a single membership's string
        // in-place, e.g. `power_var_num_unwinding_mem`'s power-token
        // peel at a directional end of `m_str`, where the change is not
        // a substitution for some other facet's variable but a direct
        // edit of this one membership's own term.
        void replace(unsigned idx, expr_ref_vector const& new_str, eq_tree::dep_tracker dep = nullptr);
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // Toggled (trailed) by mem_monadic_split once it has certified
        // the current membership set as a satisfiable conjunction of
        // per-variable views; see class comment on m_is_satisfied.
        void set_is_satisfied(bool b);

        stx::facet_i* clone(trail_stack& trail) const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;

        bool is_satisfied() const override { return m_mems.empty() || m_is_satisfied; }
        std::ostream& display(std::ostream& out) const override;
    };

    class mem_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&    m;
        seq_util&       u;
        seq_rewriter&   m_rw;
        live_states&    m_live;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        mem_propagation(ast_manager& m, seq_util& u, seq_rewriter& rw, live_states& live) :
            m(m), u(u), m_rw(rw), m_live(live) {}
        char const* name() const override { return "mem-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("mem-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Forwards ambient-context length bounds (lower/upper bounds on
    // `str.len(x)` known to the surrounding arithmetic theory, together
    // with their justifying dependency) as membership constraints on the
    // corresponding sequence variable: `x in (allchar){lo,hi}` (or an
    // open lower/upper variant when only one side is known). This lets
    // e.g. `mem_var_split`'s fresh split variables inherit whatever
    // length obligations the sub-solver has already derived for the
    // parent variable's remaining suffix/prefix, instead of only ever
    // seeing them through arithmetic constraints that regex-side rules
    // do not consult.
    //
    // Runs as an ordinary propagation plugin (every node, to fixpoint
    // alongside every other propagation plugin) rather than a one-shot
    // "root only" step: per node this naturally also picks up any
    // *tighter* bound the sub-solver has derived for a variable it saw
    // before (e.g. after further splits narrow it), not just the first
    // bound ever seen for that variable. Idempotency (required by
    // `propagation_plugin_i`'s confluence contract) is maintained by
    // remembering, per variable, the last (lo, hi) pair whose membership
    // was actually added, in a trail-managed map that is unwound on
    // backtrack along with everything else - so a repeated query that
    // yields the same bound is skipped (`noop`) and only a strictly
    // tighter bound triggers a fresh membership add.
    class mem_bounds_propagation : public eq_tree::propagation_plugin_i {
    public:
        // Last (lo, hi) bound pair for which a membership was already
        // added for a given variable, so unchanged bounds are skipped.
        // Public: referenced by mem_bounds_last_trail (seq_mem_facet.cpp),
        // this plugin's own trail-undo object for `m_last`.
        struct last_bound { rational lo, hi; bool has_lo = false, has_hi = false; };

    private:
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        trail_stack&  m_trail;

        obj_map<expr, last_bound> m_last;

        struct stats {
            unsigned m_num_propagate = 0;
            unsigned m_num_added = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Collect the candidate sequence variables currently live in
        // this node: those appearing in eq_facet's equations (both
        // sides) and mem_facet's own membership tokens - the only two
        // facets that expose variable-bearing token vectors today.
        void collect_vars(eq_tree::node& n, obj_hashtable<expr>& vars) const;

    public:
        mem_bounds_propagation(ast_manager& m, seq_util& u, arith_util& a, trail_stack& trail) : m(m), u(u), a(a), m_trail(trail) {}
        char const* name() const override { return "mem-bounds-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("mem-bounds-propagate num calls", m_stats.m_num_propagate);
            st.update("mem-bounds-propagate num added", m_stats.m_num_added);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Membership-side analog of `power_var_peel` (seq_power_facet.h),
    // ported from the c3 branch's `seq_nielsen_modifiers.cpp`
    // `apply_var_num_unwinding_mem` (facet-eq-deq.md /
    // facet-membership.md). Trigger pattern: some mem_facet membership's
    // own flattened string has a power token `U^n` at a directional end
    // (front or back) - unlike the eq-side rule, no "opposite side is a
    // variable" check applies, since a membership has only one string
    // operand (see class comment on power_var_peel for the shared
    // two-branch structure this mirrors). Skipped if `n` is already a
    // resolved numeral (power_propagation's known-exponent branch
    // handles that case directly).
    //
    // Branch 1 (n=0): U^n -> epsilon, single side constraint `n=0`
    // (c3's mem-variant uses one `mk_eq(exp_n, zero)` clause, not the
    // eq-variant's two-clause `n>=0 /\ n<=0` - preserved faithfully per
    // rule variant, see facet-eq-deq.md).
    // Branch 2 (n>=1): peel one copy, U^n -> U . U^(n-1) (or reversed,
    // matching directional end), spliced directly into the
    // membership's own string via `mem_facet::replace` (not
    // `broadcast_subst`, since the power token here may be a sub-token
    // of a larger concatenation on the membership's string, and
    // `mem_facet::apply_subst`'s exact-whole-string-match semantics
    // cannot splice a sub-token in place).
    class power_var_peel_mem : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_mem_idx;
            bool           m_fwd;
            unsigned       m_pow_idx;
            eq_tree::dep_tracker m_dep;
            bool           m_done = false;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      unsigned mem_idx, bool fwd, unsigned pow_idx,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n),
                m_mem_idx(mem_idx), m_fwd(fwd), m_pow_idx(pow_idx),
                m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_var_peel_mem(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-var-peel-mem"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("power-var-peel-mem num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    class mem_monadic_split : public eq_tree::split_plugin_i {
        ast_manager&      m;
        seq_util&         u;
        seq_rewriter&     m_rw;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node&             m_n;
            // Private trail, entirely separate from the search tree's shared trail:
            // seq_monadic::add() pushes undo-trail entries referencing its own
            // internal state, and those entries must stay valid for exactly as
            // long as m_mon itself does. Tying them to the search tree's shared
            // trail is unsafe, since a declining split() call is immediately
            // followed by that shared scope being popped (see extend_node()'s
            // scoped_push), which would run these entries' undo() against an
            // already-destroyed seq_monadic. A private trail/engine pair, owned
            // and torn down together by this iterator, avoids that entirely.
            trail_stack                m_priv_trail;
            seq_monadic                m_mon;
            // Constructed in the body (after m_mon.add() populates the
            // engine), not the initializer list: seq_monadic::iterate()
            // snapshots the engine's CURRENT membership set, so building
            // it before add() runs would capture an empty conjunction.
            scoped_ptr<seq_monadic::iterator> m_it;
            bool                       m_first_pending = true;
            obj_map<expr, seq::view_vector> m_first;
            ast_manager&               m;
            seq_util&                  u;

        public:
            iterator(eq_tree::node& n, seq_rewriter& rw, ast_manager& m, seq_util& u,
                     vector<str_mem> const& mems);
            bool next(eq_tree::edge& out) override;
            bool has_first() const { return !m_first.empty(); }
        };

    public:
        mem_monadic_split(ast_manager& m, seq_util& u, seq_rewriter& rw, trail_stack& trail) :
            m(m), u(u), m_rw(rw) {}
        char const* name() const override { return "mem-monadic"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("mem-monadic num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

}
