/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.h

Abstract:

    Positive regular-expression membership facet.

    A `str_mem` constrains one sequence term against a `seq::view`: either a
    plain membership `<state,null>` meaning the whole term is in the language
    of `state`, or a reach view `<state,target>` meaning the term drives the
    derivative automaton from `state` to `target`.

    Deterministic checks use `seq::accepts`, `seq::is_dead`, and
    `seq::live_states`. Splitting is delegated to `mem_split`, which
    decomposes one membership at a time into per-variable views, and
    `view_witness`, which checks joint feasibility of the accumulated views.
    Substitutions chosen elsewhere are broadcast through `subst_sink_i` so
    pending memberships stay synchronized with the shared variable pool.

    This facet does not implement regex factorization. Membership-side
    splitting is driven entirely by `mem_monadic_split`, which narrows views
    one membership at a time and leaves witness materialization to
    `view_witness`.

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
#include <vector>
#include <utility>

namespace seq {

    struct str_mem : public stx::constraint_i {
        expr_ref_vector      m_str;
        view                 m_view;
        eq_tree::dep_tracker m_dep = nullptr;
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

        // -- stx::constraint_i (unsat-cache identity) --
        // Identity is (token list, view): the same string term driving
        // the same (state,target) automaton view. `clone()` intentionally
        // drops `m_dep`/`m_active` - see stx::constraint_i's class
        // comment - and recovers the ast_manager it needs from
        // `m_str`'s own ref-vector (str_mem itself holds no separate
        // `ast_manager&` member).
        uint64_t hash() const override;
        bool equals(stx::constraint_i const& other) const override;
        stx::constraint_i* clone() const override { return alloc(str_mem, m_str.get_manager(), m_str, m_view); }
        void* dep_handle() const override { return m_dep; }
    };

    class mem_facet : public stx::facet_i, public subst_sink_i {
        ast_manager&      m;
        seq_util&         u;
        eq_tree::dep_manager_t& m_dm;
        seq_rewriter&     m_rw;
        live_states       m_live;
        vector<str_mem>   m_mems;
        view_witness      m_vw;
        mutable unsigned  m_vw_budget = 0;

        unsigned          m_qhead = 0;
        // Incremental cursor for `mem_var_bounds_propagation`, separate
        // from `m_qhead` (owned by `mem_propagation`'s derivative scan).
        unsigned          m_bounds_qhead = 0;

        bool              m_witness_extracted = false;
        obj_map<expr, expr*> m_witness;
        expr_ref_vector   m_witness_pin;
        ambient_context_i<eq_tree::dep_tracker>& m_ac;

    public:
        mem_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm, seq_rewriter& rw,
                  ambient_context_i<eq_tree::dep_tracker>& ac) :
            facet_i(trail), m(m), u(u), m_dm(dm), m_rw(rw), m_live(rw),
            m_vw(trail, rw, m_live, transition_mode::brzozowski_tm), m_witness_pin(m), m_ac(ac) {
            m_vw.set_checkpoint([this]() {
                if (!this->m.limit().inc())
                    return view_failure_reason::resource;
                return ++m_vw_budget > 2000000 ? view_failure_reason::budget : view_failure_reason::none;
            });
        }

        void reset_vw_budget() const { m_vw_budget = 0; }

        unsigned qhead() const { return m_qhead; }

        void advance_qhead(unsigned head);

        unsigned bounds_qhead() const { return m_bounds_qhead; }

        void advance_bounds_qhead(unsigned head);

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        live_states& live() const { return const_cast<live_states&>(m_live); }
        eq_tree::dep_manager_t& dm() const { return m_dm; }
        vector<str_mem> const& memberships() const { return m_mems; }
        view_witness& vw() { return m_vw; }

        bool is_single_var_plain(str_mem const& sm) const {
            return sm.m_str.size() == 1 && m_ac.is_var(sm.m_str.get(0));
        }

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
        void remove(unsigned idx);
        void replace(unsigned idx, expr_ref_vector const& new_str, eq_tree::dep_tracker dep = nullptr);
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        stx::facet_i* clone(trail_stack& trail) const override;

        bool is_satisfied() const override;
        std::ostream& display(std::ostream& out) const override;

        // -- unsat-cache signature --
        // Regex memberships (state, target) determine (in)consistency
        // directly, so they always participate.
        bool contributes_to_signature() const override { return true; }
        void append_constraints(vector<stx::constraint_i const*>& out) const override;
    };

    class mem_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&    m;
        seq_util&       u;
        seq_rewriter&   m_rw;
        // Optional end-game witness solver, gated by
        // smt.seq.mem_monadic_endgame. Once `f.is_satisfied()` holds, it
        // decides all active plain memberships jointly with `seq::monadic`
        // instead of asking `view_witness` for per-variable witnesses.
        // Uses a private scratch trail scoped per call.
        trail_stack     m_mon_trail;
        seq::monadic    m_mon;
        struct stats {
            unsigned m_num_propagate = 0;
            unsigned m_num_monadic_asked = 0;
            unsigned m_num_monadic_refuted = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Runs the monadic end-game solver over every active plain
        // membership in `f`, adding exact length assumptions when the
        // arithmetic sub-solver already assigns one. `l_false` means the
        // conjunction is refuted and `dep` is the joined core; `l_true`
        // means witnesses were materialized into `f`; `l_undef` means the
        // solver could not decide and the caller should fall back to
        // `view_witness`.
        lbool solve_monadic_endgame(ambient_ref<eq_tree::node, eq_tree::dep_tracker>& ac, mem_facet& f, eq_tree::dep_tracker& dep);
    public:
        mem_propagation(ast_manager& m, seq_util& u, seq_rewriter& rw) :
            m(m), u(u), m_rw(rw), m_mon(rw, m_mon_trail) {}
        char const* name() const override { return "mem-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-propagate num calls", m_stats.m_num_propagate);
            st.update("seq-mem-monadic-endgame num asked", m_stats.m_num_monadic_asked);
            st.update("seq-mem-monadic-endgame num refuted", m_stats.m_num_monadic_refuted);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Forwards arithmetic bounds on `str.len(x)` as membership constraints
    // `x in (allchar){lo,hi}` (or one-sided variants), so regex-side rules
    // (view_witness, seq::monadic) see the current length bounds directly
    // instead of only inferring them from a model round-trip.
    //
    // Processes `str_mem` constraints incrementally: `m_bounds_qhead`
    // (owned by `mem_facet`) tracks which memberships have already been
    // scanned. For each variable in a newly scanned membership, if the
    // ambient context currently has a lower and/or upper bound on its
    // length, a bound membership is added once and the variable is marked
    // done in `m_done` (a trail-managed set shared across the whole
    // search, mirroring how variable identity is shared). A later,
    // tighter bound is not re-forwarded: the wider membership already
    // added remains a sound (if less precise) constraint. If no bound is
    // known yet, the variable is left unmarked and may still be picked up
    // later if it recurs in a fresh membership (e.g. produced by a split
    // or substitution).
    class mem_var_bounds_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        trail_stack&  m_trail;

        // Variables that already have a bound membership forwarded; never
        // re-added, see class comment.
        obj_hashtable<expr> m_done;

        struct stats {
            unsigned m_num_propagate = 0;
            unsigned m_num_added = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

    public:
        mem_var_bounds_propagation(ast_manager& m, seq_util& u, arith_util& a, ambient_context_i<eq_tree::dep_tracker>& ac) : m(m), u(u), a(a), m_trail(ac.trail()) {}
        char const* name() const override { return "mem-bounds-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-bounds-propagate num calls", m_stats.m_num_propagate);
            st.update("seq-mem-bounds-propagate num added", m_stats.m_num_added);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Length/Parikh feasibility check. It combines the `len_abs`
    // abstractions of multiple plain memberships on the same variable and
    // refutes the node if their meet is empty.
    //
    // This is a `split_plugin_i` because it is purely a cheap refutation
    // gate: it either reports conflict or declines.
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

    // Peel a power token `U^n` at a directional end of a membership:
    // `n <= 0` gives `epsilon`, `n >= 1` gives `U . U^(n-1)`. Both
    // branches go through `broadcast_subst`.
    class power_peel_mem : public eq_tree::split_plugin_i {
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
        power_peel_mem(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-peel-mem"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-peel-mem num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Decompose one membership `term in R` into branches. Each branch is a
    // vector of `(variable, view)` pairs: a reach view for a variable
    // followed by more of the term, or a membership view for a variable
    // that ends it.
    //
    // This class only performs the decomposition. It does not test whether
    // views for the same variable are jointly feasible; that is
    // `view_witness`'s job.
    class mem_split {
    public:
        struct elem {
            expr_ref var;
            view     m_view;
            elem(expr_ref const& v, view const& w) : var(v), m_view(w) {}
        };
        using branch = vector<elem>;

        // Lazily enumerates the branches prepared by the last iterate()
        // call. Only one iterator may be live per `mem_split`; `m_gen`
        // makes stale iterators report exhaustion.
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
        // One frame per variable atom on the current branch. Frames form an
        // explicit stack so a leaf can be resumed by the iterator.
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

        // Work budget for one iterate() call.
        void set_budget(unsigned b) { m_budget_limit = b; }

        // True when `str` contains a seq.unit of a non-value, which this
        // class cannot decompose.
        bool can_decide(expr_ref_vector const& str);

        // Begin decomposing the already-flattened atom stream `str`
        // against `v`. Invalidates any iterator from a previous call. If
        // `str` contains an unsupported element, the returned iterator
        // reports `gave_up()` immediately.
        iterator iterate(expr_ref_vector const& str, view const& v);
    };


    // Decomposes one active membership at a time. `split()` picks the
    // cheapest active membership that is not already a single-variable
    // plain membership, then materializes one `mem_split` branch by
    // replacing it with fresh single-variable memberships. Joint
    // feasibility across memberships is handled by `view_witness` in
    // `mem_facet`, not here.
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
            // `next()` returning no branch may mean either "refuted" or
            // "gave up"; `gave_up()` disambiguates that for `split()`.
            bool gave_up() const { return m_it.gave_up(); }
            eq_tree::dep_tracker dep() const { return m_dep; }
        };

        // Find the cheapest active membership that is not already a
        // single-variable view. Cost counts only non-unit atoms, which
        // are the actual branching points.
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

    // Whole-conjunction decision rule. Unlike `mem_monadic_split`, which
    // decomposes one membership at a time, this rule feeds every active
    // plain membership into one `seq::monadic` instance and asks it to
    // decide the whole conjunction.
    //
    // `m_declined_here` prevents the unchanged branch from refiring on the
    // same subtree; it is trailed on the shared node trail and cleared on
    // backtrack.
    //
    // Two outcomes on check():
    //  - `l_false`: the memberships alone are inconsistent, so the whole
    //    node is inconsistent.
    //  - `l_true`: only useful once eq/deq facets are already satisfied.
    //    The rule then pins each variable to a witness equation in one
    //    branch and leaves an unchanged fallback branch guarded by
    //    `m_declined_here`.
    class mem_leaf_split : public eq_tree::split_plugin_i {
        ast_manager&        m;
        seq_util&           u;
        trail_stack         m_mon_trail;   // private scratch trail, scoped per check() via push/pop_scope
        seq::monadic        m_mon;
        unsigned            m_budget;
        unsigned            m_budget_root;
        bool                m_declined_here = false;
        // Not trailed: reset once per outer search by `reset_root_ask()`.
        bool                m_root_asked = false;
        struct stats {
            unsigned m_num_asked = 0;
            unsigned m_num_refuted = 0;
            unsigned m_num_committed = 0;
            unsigned m_num_cache_hits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Cache `ask()` results by the sorted `(term, regex)` pairs fed to
        // the solver. The verdict depends only on that set, so entries are
        // valid across backtracking for the plugin's lifetime.
        struct leaf_cache_entry {
            std::vector<std::pair<expr*, expr*>> key;   // sorted `(term, regex)` pairs
            lbool                                 result;
            bool                                   has_witnesses = false;
            expr_ref_vector                        wit_vars;
            expr_ref_vector                        wit_words;
            leaf_cache_entry(ast_manager& m, std::vector<std::pair<expr*, expr*>> k, lbool r) :
                key(std::move(k)), result(r), wit_vars(m), wit_words(m) {}
        };
        std::vector<leaf_cache_entry> m_cache;

        leaf_cache_entry* find_cache(std::vector<std::pair<expr*, expr*>> const& key) {
            for (auto& e : m_cache)
                if (e.key == key)
                    return &e;
            return nullptr;
        }

        // Record a fresh verdict for `key`. When non-null, `witnesses` is
        // replayed on future `l_true` cache hits that also need witnesses.
        void cache_insert(std::vector<std::pair<expr*, expr*>> const& key, lbool result, expr_substitution* witnesses) {
            m_cache.emplace_back(m, key, result);
            leaf_cache_entry& e = m_cache.back();
            if (witnesses) {
                e.has_witnesses = true;
                for (auto const& entry : witnesses->sub()) {
                    e.wit_vars.push_back(&entry.get_key());
                    e.wit_words.push_back(entry.get_value());
                }
            }
        }

        // Ask the monadic engine about every active plain membership in
        // `mf`. On `l_false`, `all_dep` is replaced by the minimized core.
        // On `l_true`, `all_dep` is the joined dependency of the fed
        // memberships and `witnesses`, when requested, receives the joint
        // solution. Returns `l_undef` when nothing was fed or the solver
        // could not decide.
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

        // Called before each outer search to re-enable the root-only
        // refutation ask, even while equations are pending.
        void reset_root_ask() { m_root_asked = false; }

        void collect_statistics(::statistics& st) const override {
            st.update("seq-mem-leaf num asked", m_stats.m_num_asked);
            st.update("seq-mem-leaf num refuted", m_stats.m_num_refuted);
            st.update("seq-mem-leaf num committed", m_stats.m_num_committed);
            st.update("seq-mem-leaf num cache hits", m_stats.m_num_cache_hits);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

}
