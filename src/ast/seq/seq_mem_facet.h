/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.h

Abstract:

    Positive regular-expression membership facet ("Phase 5" of the modular
    plugin-based search tree design, following `stx::` in
    util/stx_search_tree.h and the `eq_facet`/`deq_facet` and `solver_facet`
    modules).

    A `str_mem` constrains one sequence term against a `seq::view`: either a
    plain membership `<state,null>` meaning the whole term is in the language
    of `state`, or a reach view `<state,target>` meaning the term drives the
    derivative automaton from `state` to `target`.

    This port deliberately keeps the facet small and delegates regex-specific
    search to already-existing components:
      - deterministic discharge / conflict checks use `seq::accepts`,
        `seq::is_dead`, and `seq::live_states`;
      - multi-view landing splits are delegated to `mem_split` (decomposes
        one membership at a time into per-variable views) combined with
        `view_witness` (per-variable view-intersection non-emptiness),
        both defined in this file;
      - substitutions chosen by `word_eq_split` are broadcast here through
        `subst_sink_i`, so pending memberships stay synchronized with the
        shared variable pool.

    Scope note / simplifications relative to the full design:
      - regex factorization (§4.2 of facet-membership.md) is NOT implemented
        in this pass;
      - the c3 branch's `apply_regex_var_split` (a per-membership
        Nielsen-style variable split, `x -> epsilon` / `x -> c.x'`) is not
        ported here: monadic landing (`mem_monadic_split`, driven by
        `mem_split` + `view_witness`) subsumes it as the sole
        membership-side splitting rule, so no standalone `mem_var_split`
        class exists in this port;
      - monadic landing is implemented for the conjunction of memberships
        currently present in `mem_facet`; it narrows views reported by
        per-membership `mem_split::iterator`s and leaves exact witness
        materialization to `view_witness` itself. Unlike the earlier
        `seq_monadic`-based engine, there is no orientation retry
        (forward/reversed) or intersection-decomposition refinement pass -
        those were seq_monadic-specific policies layered on top of its
        joint search, not part of the one-membership-at-a-time
        decomposition this port now uses.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_view.h"
#include "ast/seq/seq_regex_live.h"
#include "ast/seq/seq_view_witness.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/seq/seq_monadic.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_substitution.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include "util/obj_pair_hashtable.h"

namespace seq {

    struct str_mem {
        expr_ref_vector      m_str;
        view                 m_view;
        eq_tree::dep_tracker m_dep = nullptr;
        // Append-only representation: m_mems is never erased/shifted
        // (mirrors power_facet::str_power::m_active / eq_facet's
        // discipline). "Removing" a membership just flips m_active to
        // false (trailed via value_trail, restored on backtrack); no
        // index is ever invalidated by a removal elsewhere. This matters
        // here specifically because power_var_peel_mem's iterator
        // persists a raw m_mem_idx across next() calls that span DFS
        // branch resumptions. Consumers that iterate memberships() must
        // skip entries with !active().
        bool                 m_active = true;

        str_mem(ast_manager& m, expr* s, view const& v, eq_tree::dep_tracker dep = nullptr) :
            m_str(m), m_view(v), m_dep(dep) {
            seq_util(m).str.get_concat_units(s, m_str);
        }
        str_mem(ast_manager& m, expr_ref_vector const& ts, view const& v, eq_tree::dep_tracker dep = nullptr) :
            m_str(ts), m_view(v), m_dep(dep) {}

        bool is_plain() const { return m_view.is_membership(); }
        bool is_view() const { return m_view.is_reach(); }
        bool active() const { return m_active; }
    };

    class mem_facet : public stx::facet_i, public subst_sink_i {
        ast_manager&      m;
        seq_util&         u;
        eq_tree::dep_manager_t& m_dm;
        seq_rewriter&     m_rw;
        live_states       m_live;
        vector<str_mem>   m_mems;
        // Incrementally tracks every active plain membership whose own
        // string is already a single bare variable (`x in R`): add()
        // registers it here as soon as it is added (see
        // is_single_var_plain() in seq_mem_facet.cpp), so the joint
        // feasibility of every such constraint - across however many
        // originally-distinct memberships produced views on the same
        // variable - is checked incrementally by mem_propagation via
        // m_vw.check(), instead of being recomputed from scratch by
        // mem_monadic_split on every split() call. Uses this facet's own
        // (shared, ambient) trail, so add()'s bookkeeping backtracks in
        // lockstep with m_mems automatically. narrow()/replace()/
        // apply_subst() never unregister a stale entry when they
        // deactivate a membership (append-only, like m_mems itself) -
        // the surviving fact stays true and is harmless to keep around.
        view_witness      m_vw;
        // Work counter backing m_vw's checkpoint (see the constructor):
        // product_nonempty()'s state-expansion search has no bound of its
        // own and relies entirely on the checkpoint callback to cut off a
        // search over a cyclic/unbounded view (e.g. `x in (ab)+` alone),
        // so m_vw must have one installed - mirrors seq_monadic's own
        // m_budget/out_of_budget (seq_monadic.h), which every OTHER
        // view_witness in this codebase is given at construction time.
        mutable unsigned  m_vw_budget = 0;

        // First not-yet-fully-examined index into m_mems for
        // mem_propagation's per-membership structural scan (mirrors
        // req_facet's/ncontains_facet's own m_qhead convention): a round
        // only re-scans [m_qhead, m_mems.size()), never the whole vector
        // from scratch. No rewind hook is needed here (unlike
        // ncontains_facet's apply_subst, which mutates an existing
        // entry's token vectors in place): every mutator that ever
        // touches an existing membership - narrow(), replace(), and
        // apply_subst() - is built entirely on remove()+add() (see their
        // definitions), so a membership below m_qhead can only ever be
        // deactivated, never have its m_str/m_view changed in place; any
        // actual update always appears as a brand-new entry appended
        // past the current size, which is >= m_qhead by construction and
        // so is naturally still ahead of the qhead when it is reached.
        // Trailed via advance_qhead(), so it unwinds with everything else
        // on backtrack.
        unsigned          m_qhead = 0;

        bool              m_witness_extracted = false;
        obj_map<expr, expr*> m_witness;
        expr_ref_vector   m_witness_pin;

    public:
        mem_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm, seq_rewriter& rw) :
            facet_i(trail), m(m), u(u), m_dm(dm), m_rw(rw), m_live(rw),
            m_vw(trail, rw, m_live, transition_mode::brzozowski_tm), m_witness_pin(m) {
            m_vw.set_checkpoint([this]() {
                if (!this->m.limit().inc())
                    return view_failure_reason::resource;
                return ++m_vw_budget > 2000000 ? view_failure_reason::budget : view_failure_reason::none;
            });
        }
        // Resets the per-check() work counter backing m_vw's checkpoint
        // (see m_vw_budget's comment): called by mem_propagation right
        // before vw().check(), so each round gets a fresh budget rather
        // than a single lifetime allowance for the whole search.
        void reset_vw_budget() const { m_vw_budget = 0; }

        // See m_qhead's comment: mem_propagation's per-membership scan
        // uses these to avoid rescanning already-examined entries.
        unsigned qhead() const { return m_qhead; }
        // Advance m_qhead to `head` (only ever forward via this call;
        // trailed so it un-advances correctly on backtrack).
        void advance_qhead(unsigned head);

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        live_states& live() const { return const_cast<live_states&>(m_live); }
        eq_tree::dep_manager_t& dm() const { return m_dm; }
        vector<str_mem> const& memberships() const { return m_mems; }
        // Every active plain single-variable membership registered so
        // far (see m_vw's comment above); mem_propagation calls
        // vw().check() each round and reports a conflict from vw().core()
        // on l_false.
        view_witness& vw() { return m_vw; }

        // See m_witness/m_witness_extracted's comment above.
        bool witness_extracted() const { return m_witness_extracted; }
        void set_witness_extracted(bool v = true);
        void set_witness(expr* var, expr* w);
        bool get_witness(expr* var, expr_ref& w) const;
        // Model construction: for every active single-variable plain
        // membership `x in R` with a materialized witness (see
        // get_witness), insert `x -> witness` into `subst` and pin the
        // witness in `pin` (both owned by the caller, typically with the
        // same lifetime as the model being built).
        void get_witness_model(obj_map<expr, expr*>& subst, expr_ref_vector& pin) const;

        void add(str_mem const& sm);
        void narrow(unsigned idx, view const& new_view);
        // Drop `idx`'s membership entirely. Trailed: this just flips
        // m_active to false via a value_trail (restored to true on
        // backtrack) - append-only, no shifting, no index invalidation
        // for any other facet/iterator holding onto `idx` (see
        // str_mem::m_active comment).
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

        stx::facet_i* clone(trail_stack& trail) const override;

        // True once there is no active plain membership left for
        // mem_monadic_split to decompose - i.e. every active plain
        // membership is already a single-variable view (or there are no
        // active memberships at all). This says nothing about whether
        // those single-variable views are jointly satisfiable - that is
        // m_vw/mem_propagation's job, checked incrementally and reported
        // as an ordinary conflict, so a node that reaches this predicate
        // without having already conflicted is known consistent.
        bool is_satisfied() const override;
        std::ostream& display(std::ostream& out) const override;
    };

    class mem_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&    m;
        seq_util&       u;
        seq_rewriter&   m_rw;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        mem_propagation(ast_manager& m, seq_util& u, seq_rewriter& rw) :
            m(m), u(u), m_rw(rw) {}
        char const* name() const override { return "mem-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-mem-propagate num calls", m_stats.m_num_propagate); }
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
        mem_bounds_propagation(ast_manager& m, seq_util& u, arith_util& a, ambient_context_i<eq_tree::dep_tracker>& ac) : m(m), u(u), a(a), m_trail(ac.trail()) {}
        char const* name() const override { return "mem-bounds-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-bounds-propagate num calls", m_stats.m_num_propagate);
            st.update("seq-mem-bounds-propagate num added", m_stats.m_num_added);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Length/Parikh feasibility check, ported (in spirit) from the c3
    // branch's `seq_parikh` congruence-abstraction engine, but built as a
    // thin wrapper over infrastructure this port already has:
    // `seq_util::rex::info`/`util/len_abs.h`'s `len_abs` compute a sound
    // ultimately-periodic over-approximation of a regex's admissible word
    // lengths structurally, so this plugin only has to combine the
    // per-membership abstractions already reachable via
    // `u.re.get_info(view.m_state).len()` and check the meet for
    // emptiness - no separate hand-rolled length/stride reasoning is
    // needed (see len_abs.h's module comment: (a^4)* meet (b^6)* type
    // refutations - e.g. two plain memberships on the same variable whose
    // period/residue sets disagree - are exactly what this abstraction is
    // for).
    //
    // Trigger: some variable carries two or more PLAIN membership views
    // (`str_mem::is_plain()`, i.e. `x in R_i`, not a reach view) whose
    // combined (meet of) length abstractions is certified empty by
    // `len_abs::is_empty()` - a sound refutation, since every value of
    // `x` must lie in the length set of every `R_i` simultaneously.
    //
    // Implemented as a `split_plugin_i` (not a propagation plugin), per
    // the same rationale as `eq_approx_split`: this is a pure refutation
    // gate (it never commits a branch, only ever calls
    // `n.set_conflict()` or declines), so it must run at a low
    // `min_cost()` ahead of every other, more expensive branching rule
    // rather than eagerly firing every propagation fixpoint round -
    // mirroring how c3 invokes its own Parikh feasibility check ahead of
    // `generate_extensions` rather than folding it into ordinary
    // constraint propagation.
    class mem_parikh_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        struct stats {
            unsigned m_num_checks = 0;
            unsigned m_num_refuted = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        mem_parikh_split(ast_manager& m, seq_util& u) : m(m), u(u) {
            set_min_cost(0);
        }
        char const* name() const override { return "mem-parikh-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-parikh-split num checks", m_stats.m_num_checks);
            st.update("seq-mem-parikh-split num refuted", m_stats.m_num_refuted);
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
        void collect_statistics(::statistics& st) const override { st.update("seq-power-var-peel-mem num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Self-contained monadic decomposition of ONE membership constraint
    // `term in R` into an iterator of branches, each branch being the
    // vector of (variable, view) pairs the search commits to for every
    // variable occurrence in `term` - a reach view <state,target> for a
    // variable followed by more of the term, a membership view
    // <state,null> for a variable that ends it (see seq_view.h).
    //
    // This class deliberately does ONLY the decomposition: it never
    // tests whether the views it hands out for a given variable have a
    // non-empty intersection with views coming from elsewhere (e.g. the
    // same variable's occurrence in a DIFFERENT membership, or an
    // ambient length bound) - that is `view_witness`'s job
    // (seq_view_witness.h), which a caller combining several
    // memberships (see mem_monadic_split below) consults once it has
    // accumulated a variable's views across however many mem_split
    // instances it drives. Folding that check in here would duplicate
    // view_witness and reintroduce exactly the conflation seq_monadic
    // had between single-membership decomposition and joint
    // (multi-membership) solving.
    //
    // Mirrors seq_monadic's derivative-stepping DFS (advance_pos /
    // push_frame / commit_next / run_search), specialized to a single
    // membership: there is exactly one atom stream and no per-variable
    // group bookkeeping.
    class mem_split {
    public:
        struct elem {
            expr_ref var;
            view     m_view;
            elem(expr_ref const& v, view const& w) : var(v), m_view(w) {}
        };
        using branch = vector<elem>;

        // Lazily enumerates the branches of the decomposition prepared by
        // the last iterate() call.  Only ONE iterator may be in flight for
        // a given mem_split at a time (a fresh iterate() call throws away
        // the previous search's stack) - `m_gen` detects a stale iterator
        // and makes it report exhausted rather than resume garbage state.
        //
        // next() returning false with gave_up() false means the
        // decomposition of this membership is fully exhausted, i.e. the
        // membership itself is UNSAT. gave_up() true means the search hit
        // a resource bound (budget, live-state cap, or an inconclusive
        // nullability/guard test) before finishing, so a false result
        // proves nothing.
        class iterator {
            mem_split* m_e;
            unsigned   m_gen;
            bool       m_started = false;
        public:
            explicit iterator(mem_split& e) : m_e(&e), m_gen(e.m_gen) {}
            bool next(branch& out);
            bool gave_up() const { return m_gen != m_e->m_gen || m_e->m_giveup || m_e->m_any_undef; }
        };

    private:
        // One frame per variable atom on the branch currently being built;
        // frames form an explicit stack so a leaf can be left standing and
        // resumed later by the iterator (mirrors seq_monadic::frame,
        // narrowed to a single membership: no `mi`/`vi`/`finalize`/`undef`
        // bookkeeping, since there is one membership and no cross-variable
        // grouping here).
        struct frame {
            unsigned i;             // atom index this frame stands on
            expr*    R;             // derivative state entering atom i
            unsigned next = 0;      // next live state (or one-shot flag for the last atom) to try
            bool     last_atom;     // atom i ends the term: exactly one candidate (a membership view)
        };

        ast_manager&    m;
        seq_util&       u;
        seq_rewriter&   m_rw;
        live_states&    m_live;
        th_rewriter     m_thrw;                       // normalizes constant-element derivatives
        expr_ref_vector m_pin;                        // keeps derivative states / regexes alive
        obj_pair_map<expr, expr, expr*> m_der_cache;   // memoizes der_elem per (regex, element)

        // The already-flattened atom stream, taken verbatim from
        // str_mem::m_str (a concatenation of sequence variables and
        // seq.unit-of-value elements; no concat, string literal, or empty
        // sequence terms remain after str_mem's own construction via
        // seq_util::str::get_concat_units). There is no separate boolean
        // "is variable" tag here: at each position, u.str.is_unit(t, e)
        // distinguishes a constant element from a variable atom.
        expr_ref_vector m_atoms;
        svector<frame> m_stack;
        branch         m_branch;

        static unsigned const FINAL_POS = UINT_MAX;   // sentinel: positioned past a final-atom view
        unsigned m_pos_i = 0;
        expr*    m_pos_R = nullptr;
        // Non-null exactly when the membership being decomposed is itself
        // a reach view (`s reaches m_target from R`) rather than a plain
        // `s in R`; the final atom's view and the all-units-consumed
        // acceptance test both need to know which is intended (see
        // final_accepts()).
        expr*    m_target = nullptr;

        unsigned m_budget = 0;
        unsigned m_budget_limit = 200000;
        bool     m_giveup = false;
        // A branch was passed over without a decisive answer (a live-state
        // enumeration hit its own cap/resource limit): running the search
        // to full exhaustion no longer refutes the membership, only fails
        // to find a satisfying branch.
        bool     m_any_undef = false;
        unsigned m_gen = 0;
        lbool    m_init_result = l_undef;

        seq_util::rex& re() const { return u.re; }

        bool out_of_budget();
        expr* der_elem(expr* r, expr* elem);
        lbool nullable(expr* r);
        // Generalizes nullable(r) to a reach view: true when reaching
        // m_target (or, for a plain membership - m_target == nullptr - the
        // usual nullability test) after consuming every atom.
        lbool final_accepts(expr* r);
        void reset_search();
        lbool advance_pos();
        bool push_frame();
        bool commit_next(frame& f);
        lbool run_search(bool backtrack);

    public:
        mem_split(ast_manager& m, seq_util& u, seq_rewriter& rw, live_states& live) :
            m(m), u(u), m_rw(rw), m_live(live), m_thrw(m), m_pin(m), m_atoms(m) {}

        // Work budget for one iterate() call (search nodes / derivative
        // steps); default matches seq_monadic's per-decision budget.
        void set_budget(unsigned b) { m_budget_limit = b; }

        // True when some element of `str` (already-flattened, e.g.
        // str_mem::m_str) is a seq.unit wrapping something other than a
        // constant value - the one shape this class cannot decompose (a
        // sequence variable, or a seq.unit of a value, are both fine).
        bool can_decide(expr_ref_vector const& str);

        // Begin decomposing the membership whose already-flattened atom
        // stream is `str` (see str_mem::m_str) against `v` (a plain
        // membership or a reach view - live_states/seq::accepts are both
        // mode-independent in the state they enumerate/test, so either
        // kind decomposes the same way, only the final acceptance test
        // differs, see final_accepts()); invalidates any iterator from a
        // previous call. If can_decide() flags `str` as containing an
        // undecidable element, the returned iterator reports gave_up()
        // immediately (defensive: mem_facet only ever holds terms this
        // class can decompose).
        iterator iterate(expr_ref_vector const& str, view const& v);
    };


    // Drives ONE active plain membership's decomposition at a time (see
    // mem_split's own class comment for what one membership's
    // decomposition means): split() picks the cheapest active plain
    // membership that is not already a single-variable view (see
    // is_single_var_plain() in seq_mem_facet.cpp - those are handled
    // directly by mem_facet's own view_witness, m_vw, and never reach
    // this class at all), and this iterator wraps a single
    // mem_split::iterator over it. Materializing a branch narrows every
    // variable occurrence in that one membership's string into a fresh
    // single-variable str_mem (mem_facet::add), which mem_facet::add()
    // then registers with m_vw itself - so cross-membership consistency
    // for a variable that occurs in several (originally distinct)
    // memberships is entirely m_vw/mem_propagation's responsibility,
    // never this class's. This intentionally removes the joint
    // multi-membership DFS the previous port of this class used to run
    // (with its own private view_witness, m_groups/m_group_deps
    // bookkeeping, and per-membership last-occurrence tracking): with
    // decomposition one-membership-at-a-time and per-variable joint
    // feasibility fully delegated to mem_facet's persistent, incrementally
    // maintained m_vw, none of that machinery is needed here anymore.
    class mem_monadic_split : public eq_tree::split_plugin_i {
        ast_manager&      m;
        seq_util&         u;
        seq_rewriter&     m_rw;
        unsigned          m_budget = 1000000;
        struct stats {
            unsigned m_num_splits = 0;
            unsigned m_num_refuted = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node&        m_n;
            ast_manager&          m;
            seq_util&             u;
            unsigned              m_mem_idx;   // index into mf.memberships() of the membership being decomposed
            eq_tree::dep_tracker  m_dep;       // that membership's own dependency
            mem_split             m_split;
            mem_split::iterator   m_it;

        public:
            iterator(eq_tree::node& n, seq_rewriter& rw, ast_manager& m, seq_util& u, live_states& live,
                     unsigned mem_idx, str_mem const& sm) :
                m_n(n), m(m), u(u), m_mem_idx(mem_idx), m_dep(sm.m_dep),
                m_split(m, u, rw, live),
                m_it(m_split.iterate(sm.m_str, sm.m_view)) {}
            bool next(eq_tree::edge& out) override;
            // See mem_split::iterator's class comment on the same
            // ambiguity: next() reporting no branch could mean either
            // "this single membership is genuinely refuted" or "gave up
            // before deciding". gave_up() disambiguates for split(),
            // which must not report a conflict on a mere give-up.
            bool gave_up() const { return m_it.gave_up(); }
            eq_tree::dep_tracker dep() const { return m_dep; }
        };

        // Finds the cheapest (fewest non-unit atoms) active membership
        // that is not already a single-variable view (plain `x in R` or
        // reach `x reaches target` alike - mem_split decomposes both, see
        // its class comment); ties broken by earliest index. Non-unit
        // atoms (variables) are what drives the combinatorial branching in
        // mem_split - unit atoms just narrow the automaton state without
        // any choice, so counting only non-units ranks by actual branching
        // cost rather than raw string length. Returns false if no such
        // membership exists (nothing left for this class to do - either
        // mf.is_satisfied() already holds, or every active membership is a
        // single-variable view whose feasibility is m_vw/mem_propagation's
        // job).
        bool find_split_target(mem_facet const& mf, unsigned& idx);

    public:
        mem_monadic_split(ast_manager& m, seq_util& u, seq_rewriter& rw, ambient_context_i<eq_tree::dep_tracker>& ac) :
            m(m), u(u), m_rw(rw), m_budget(ac.fparams().m_seq_regex_budget) {}
        char const* name() const override { return "mem-monadic"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-monadic num splits", m_stats.m_num_splits);
            st.update("seq-mem-monadic num refuted", m_stats.m_num_refuted);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Whole-language, whole-conjunction decision rule ("monadic leaf",
    // c3/z3-tacas: nielsen_graph::apply_monadic_leaf,
    // seq_nielsen_regex.cpp). Where mem_monadic_split above decomposes ONE
    // compound membership at a time (token-by-token derivative splitting,
    // driven back through mem_split/view_witness), this rule instead feeds
    // every currently active PLAIN membership (whole term, non-reach) into
    // a single `seq::monadic` engine instance and asks it to decide the
    // WHOLE conjunction in one shot - the same self-contained decision
    // procedure theory_seq's own seq_regex.cpp already uses for classic
    // seq. This matters most for "MembershipEquations"-style benchmarks,
    // where several regex-constrained variables are also linked by word
    // equations: mem_monadic_split's per-token case splitting blows up
    // combinatorially on these, while seq::monadic decides the whole
    // regex side directly and lets the resulting concrete witness settle
    // the equation side too.
    //
    // Unlike z3-tacas's nielsen_graph, this port has no persistent
    // per-branch node objects to tag "already tried, don't refire" (see
    // module comment / apply_monadic_leaf's node->is_signature_alias()
    // guard) - the search tree here reuses one mutable node throughout the
    // whole DFS. m_declined_here plays that role instead: it is set true,
    // via a value_trail pushed on the SHARED node trail, only when the
    // "unchanged" (child B) branch below is committed, so split() declines
    // outright on that exact subtree until backtracking restores it to
    // false - without needing any node-side flag.
    //
    // Two outcomes on check():
    //  - l_false: the fed memberships are a SUBSET of the node's full
    //    constraint set, so refuting them alone refutes the whole node,
    //    regardless of whatever equations/disequations are also active
    //    (mirrors nielsen_graph's `refute_only` reasoning) - this half is
    //    therefore always attempted.
    //  - l_true: only acted on when eq_facet/deq_facet are BOTH already
    //    satisfied (no active equations/disequations) - otherwise this is
    //    a relaxation (the memberships alone being satisfiable says
    //    nothing about the equations), so it is silently discarded exactly
    //    as z3-tacas's refute_only gate does. When it does apply, every
    //    variable in the joint solution is materialized to a witness word
    //    and the rule commits two branches: child A pins every variable to
    //    its witness via a fresh eq_facet equation (a sound restriction,
    //    checked like any other equation by the rest of the search); child
    //    B leaves the node completely unchanged but marks m_declined_here
    //    so this rule does not refire on it (this is what keeps the rule
    //    complete - child B still covers "the witness picked might be
    //    wrong").
    class mem_leaf_split : public eq_tree::split_plugin_i {
        ast_manager&        m;
        seq_util&           u;
        trail_stack         m_mon_trail;   // private scratch trail, scoped per check() via push/pop_scope
        seq::monadic        m_mon;
        unsigned            m_budget;
        unsigned            m_budget_root;
        bool                m_declined_here = false;
        // See split()'s comment: not trailed - a true one-time (per
        // reset_root_ask()) lifetime event, mirroring c3's
        // m_monadic_leaf_root_asked. theory_nseq resets this once before
        // every m_tree.solve() call (one "search" per final_check_eh, as
        // in c3), so a later search over a since-grown constraint set
        // gets its own root ask.
        bool                m_root_asked = false;
        struct stats {
            unsigned m_num_asked = 0;
            unsigned m_num_refuted = 0;
            unsigned m_num_committed = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Runs one ask of the engine over every active plain membership in
        // `mf`: asserts them all (in a private, immediately-popped scope
        // of m_mon_trail), calls check() under `budget`, and reports the
        // verdict. On l_false, `all_dep` is overwritten with the
        // minimized-core dependency (from m_mon.core()) - the conflict
        // justification. On l_true, `all_dep` holds the joined
        // dependency of every fed membership - the justification for any
        // equation this rule goes on to add - and, when `witnesses` is
        // non-null, every variable's joint solution is materialized into
        // it (materialize_all()); a materialization failure degrades the
        // result to l_undef. Passing `witnesses == nullptr` requests a
        // refutation-only ask (mirrors nielsen_graph's refute_only):
        // l_true is still reported (with all_dep set) but nothing is
        // materialized, letting the caller cheaply distinguish "would
        // have committed a witness" from "nothing to feed" without
        // paying materialize()'s cost. Returns l_undef if there was
        // nothing to feed (no active plain memberships decidable by the
        // engine) - callers must not treat that as "decided".
        lbool ask(mem_facet const& mf, unsigned budget, eq_tree::dep_tracker& all_dep, expr_substitution* witnesses);

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            eq_tree::dep_tracker m_dep;
            mem_leaf_split& m_owner;
            bool m_offered = false;
        public:
            iterator(eq_tree::node& n, eq_tree::dep_tracker dep, mem_leaf_split& owner) :
                m_n(n), m_dep(dep), m_owner(owner) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        mem_leaf_split(ast_manager& m, seq_util& u, seq_rewriter& rw, ambient_context_i<eq_tree::dep_tracker>& ac) :
            m(m), u(u), m_mon(rw, m_mon_trail), m_budget(ac.fparams().m_seq_monadic_leaf_budget),
            m_budget_root(ac.fparams().m_seq_monadic_leaf_budget_root) {
            m_mon.set_gen_solution(true);
            m_mon.set_orientation(seq::monadic::orientation::retry);
            m_mon.set_split_rounds(10);
        }
        char const* name() const override { return "mem-leaf"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;

        // Called once by theory_nseq right before every m_tree.solve()
        // (see split()'s comment on m_root_asked / c3's
        // monadic_leaf_root_refute): gives the next search its own
        // refutation-only root ask, even while equations are pending.
        void reset_root_ask() { m_root_asked = false; }

        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-leaf num asked", m_stats.m_num_asked);
            st.update("seq-mem-leaf num refuted", m_stats.m_num_refuted);
            st.update("seq-mem-leaf num committed", m_stats.m_num_committed);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

}
