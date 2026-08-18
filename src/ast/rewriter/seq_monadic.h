/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.h

Abstract:

    Whole-language monadic decomposition for regex membership of a term that is a
    concatenation of sequence variables and constant elements, e.g.  x.a.x in R.
    Generic in the element sort: characters are one instance, but the procedure works
    for any sequence element sort (the guard algebra falls back from the exact character
    range_predicate to a candidate-basis over the element values mentioned by the
    derivatives).

    Self-contained decision procedure: NO Nielsen splitting (seq_split), NO minterms,
    and NO materialization of reach(q) as a regex. It uses symbolic derivative
    cofactors as Brzozowski states or Brzozowski states post-processed into
    light-weight Antimirov states, and automaton product-reachability for emptiness.

    Method.  For a term  x.u in R  and the whole-language split, x drives the derivative
    automaton of R from R to some live state q, and the rest u must be accepted from q:

        x.u in R  <=>  OR_{q live} ( x reaches q in A_R  /\  u in q ).

    Decomposing u recursively (a leading constant is consumed by a derivative, a leading
    variable splits again, the last variable is a plain membership) yields a disjunction
    of conjunctions of per-variable *views* (seq::view):

      - reach view       <state0, q>     : the variable's value drives the derivative
                                           automaton from state0 to q
      - membership view  <state0, null>  : the variable's value is in L(state0)

    That disjunction is NEVER materialized as a DNF.  Materializing it costs the product
    of the per-position split degrees (and, for a conjunction of memberships, the product
    over memberships), which is the dominant cost in practice.  Instead the decomposition
    is explored as a depth-first search tree: one branch at a time, views pushed on
    entry and popped on backtracking.  A variable's accumulated views are tested for
    emptiness as soon as the search passes the variable's LAST occurrence -- the test has
    to be done anyway, and doing it there prunes the whole remaining subtree.  The search
    stops at the first satisfying leaf and reports the views it committed to (solution()).
    No word is built; materialize() collapses a variable's views to one on request.

    reach(q) is therefore NEVER built as a regex (which state-elimination would blow up
    super-polynomially for lattice-shaped automata).  Instead the constraints on a
    variable are decided directly by a lazy product-reachability search over tuples of
    view states: a product state accepts iff every reach view is at its target and every
    membership view is nullable; transitions are the product of the views' cofactor
    branches with pairwise-conjoined range guards (minterm-free).
    This stays in the product-of-state-counts regime, never the path-enumeration (k!)
    regime of regex state-elimination.

    Supports single / multiple / repeated variables.  Per-variable extra constraints
    (e.g. a base membership intersected with a length-regex) are expressed as an extra
    membership passed to `add` and decided by `check`.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/expr_substitution.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_view.h"
#include "ast/rewriter/seq_range_predicate.h"
#include "ast/rewriter/seq_regex_live.h"
#include "ast/rewriter/guard_set.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/obj_pair_hashtable.h"
#include "util/dependency.h"
#include "util/trail.h"
#include "util/statistics.h"
#include "util/vector.h"
#include <utility>
#include <tuple>
#include <map>
#include <vector>
#include <unordered_map>

class seq_monadic {
public:
    // Which end of the problem the search reads from.  Reading a membership backwards is
    // sound because w in R iff rev(w) in rev(R), and it is worth doing because the two
    // directions can have wildly different derivative-automaton sizes: .*a.{k} needs
    // 2^(k+1) states read forwards and k+2 read backwards.  The reversal is internal --
    // every membership is reinterpreted together and witnesses are turned back around on
    // the way out -- so it is never visible to the caller.  `retry` reads forwards and
    // turns a decision around only when the forward search runs out of budget, which keeps
    // the cost of the second direction to the decisions that had no answer anyway.
    enum class orientation { forward, reversed, retry };

private:
    struct config {
        seq::transition_mode m_mode;
        bool m_solution = true;   // whether solve()/check() record the solution
        bool m_min_core = true;   // whether check() minimizes the unsat core (else: all deps)
        bool m_state_search = true;  // use the state-based search driver (select next
                                     // membership by the last-expanded / most-frequent
                                     // head variable) instead of the positional DFS
        unsigned m_budget_limit = 1000000;  // value m_budget is reset to on each decide()
        orientation m_orientation = orientation::forward;

        config(seq::transition_mode mode) : m_mode(mode) {}
    };

    enum class bail_reason { unsupported, state_cap, budget, state_expansion, resource, nullability, guard, not_reversible, replay, num_reasons };

    static char const* bail_stat_name(bail_reason reason);
    static char const* bail_name(bail_reason reason);

    struct statistics {
        unsigned m_cofactor_calls = 0;
        unsigned m_states = 0;
        unsigned m_max_state_expansion = 0;  // most inner steps any single product state took
        unsigned m_bails[static_cast<unsigned>(bail_reason::num_reasons)] = {};

        void inc_bail(bail_reason reason) {
            ++m_bails[static_cast<unsigned>(reason)];
        }

        // Times the search stopped because it ran out of allotted work, as opposed to
        // meeting something it cannot decide in any direction.
        unsigned work_bails() const {
            return m_bails[static_cast<unsigned>(bail_reason::budget)] +
                   m_bails[static_cast<unsigned>(bail_reason::state_expansion)];
        }
    };

    ast_manager&    m;
    seq_rewriter&   m_rw;
    th_rewriter     m_thrw;                  // normalizes constant-element derivatives (folds
                                             // ground guards so dead states become re.empty)
    trail_stack&    m_undo_trail;
    sort*           m_seq_sort = nullptr;   // sequence sort shared by all memberships of the
                                            // problem under analysis (prepare rejects a mixture)
    sort*           m_elem_sort = nullptr;  // element sort of that sequence sort
    expr_ref_vector m_pin;                  // pins derivative states / witnesses referenced later
    unsigned        m_budget = 0;           // global work budget (search nodes + product pops)
    bool            m_giveup = false;       // set when the budget is exhausted
    config          m_config;
    statistics      m_stats;
    // var -> views, from the last decide().  Snapshotted at the sat leaf because the
    // search pops m_groups on the way out, even on success.
    obj_map<expr, seq::view_vector> m_solution;
    guard_set::cache m_rp_cache;             // cofactor guard -> range predicate
    // Interval ("t-regex") form of a state's derivative cofactors over the character sort:
    // a canonical list of disjoint ranges in increasing order, each carrying the targets
    // reachable on that range.  Built once per state and merged by the product, so the
    // product enumerates only the cells of the common refinement.
    struct ivl_range { unsigned lo, hi, first, count; };
    struct ivl_list {
        svector<ivl_range> ranges;
        ptr_vector<expr>   targets;   // ranges[i] owns targets[first .. first+count)
        bool               ok = true; // false: some guard is outside the range algebra
    };
    obj_map<expr, ivl_list*> m_ivl_cache;
    expr_ref_vector          m_ivl_pin;      // pins the states and targets the cache refers to
    ivl_list const* interval_cofactors(expr* r, expr* v0);
    void reset_ivl_cache();
    obj_pair_map<expr, expr, expr*> m_der_cache;  // memoizes der_elem per (regex, element)
    obj_map<expr, char> m_nullable_cache;   // memoizes nullability (0 false / 1 true / 2 unknown);
                                            // seq_rewriter's own cache is capped and flushed whole
    using membership_vec = vector<std::tuple<expr_ref, expr_ref, void*>>;

    // ---- lazy branch enumeration (see the public `iterator`) ----------------------
    // One branching decision: cursor `mi`, at derivative state `state`, continues at
    // `target`.  Recorded by TERM IDENTITY, never by position in the live-state
    // enumeration, so a replay that no longer finds its choice is detected instead of
    // silently taking a different one.  Forced continuations are not recorded.
    struct choice { unsigned mi; expr* state; expr* target; };
    svector<choice>        m_cur_path;          // choices of the branch being explored
    svector<choice>        m_leaf_path;         // ... of the branch reported by the last pull
    svector<choice> const* m_resume = nullptr;  // branch to replay before continuing
    bool m_enumerate = false;   // enumeration mode: reject the replayed leaf, record paths
    bool m_in_replay = false;   // the current branch is still the replayed prefix
    bool m_had_undef = false;   // an undecided branch was passed over in this pull

    membership_vec m_memberships;           // asserted (term in regex, dep) for check()
    membership_vec m_last_search_memberships; // inputs used by the last internal decide()
    ptr_vector<void> m_core;                // dependencies of an unsat subset, filled by check() on l_false
    std::function<bool(expr *)> m_is_var;   // predicate for whether a term is a sequence variable
    lbool m_last_result = l_undef;           // result of the last public solve()/check()
    lbool m_last_search_result = l_undef;    // result of the last internal decide()
    bool m_reversed = false;                 // whether prepare() reversed the current problem
    bool m_retry_disabled = false;           // reversed retry gave up once on this query

    seq_util&      u() const { return m_rw.u(); }
    seq_util::rex& re() const { return m_rw.u().re; }

    // A term atom: a sequence variable or a constant element (a value of the element sort).
    struct atom {
        bool     is_var;
        expr_ref var;
        expr_ref elem;

        atom(ast_manager& m, bool is_var, expr* var, expr* elem) :
            is_var(is_var), var(var, m), elem(elem, m) {}
    };


    // ---- depth-first search state; valid for the duration of one decide()/solve() ----
    vector<vector<atom>>   m_atoms;         // parsed atoms, one entry per membership
    expr_ref_vector        m_regexes;       // regex of each membership (parallel to m_atoms)
    ptr_vector<expr>       m_vars;          // variables occurring in the memberships
    obj_map<expr, unsigned> m_var_idx;      // variable -> index into m_vars / m_groups
    vector<seq::view_vector> m_groups;      // views accumulated on the current branch
    svector<unsigned>      m_num_occ;       // variable -> number of occurrences (see group_complete)
    unsigned               m_undef_vars = 0;  // depth of groups whose emptiness test gave up
    // memo for the per-variable emptiness test, keyed by the sorted, deduplicated
    // signature of the variable's view group
    typedef std::vector<seq::view::sig> group_sig;
    struct group_sig_hash {
        size_t operator()(group_sig const& s) const {
            uint64_t h = 1469598103934665603ull;
            for (auto const& p : s) {
                h = (h ^ p.state) * 1099511628211ull;
                h = (h ^ p.target) * 1099511628211ull;
            }
            return static_cast<size_t>(h);
        }
    };
    group_sig m_sig_buf;                    // reused by group_nonempty (avoids allocating per lookup)
    std::unordered_map<group_sig, lbool, group_sig_hash> m_group_cache;
    seq::live_states m_live_states;

    // Names the reversed reading of a sequence variable while the search runs backwards.
    // The marker is stripped before witnesses are reported.
    func_decl_ref m_rev_decl;

    // ---- state-based search driver (see the "search state" note in the .cpp) ----
    // A membership cursor: how far membership `mi` has been consumed on the current
    // branch.  `i` is the next unconsumed atom, `R` the derivative state of the regex
    // after the consumed prefix, `complete` once every atom is consumed (and the tail is
    // known nullable / covered by a membership view).  The set of non-complete
    // cursors is the "set of active membership constraints"; each non-complete cursor has
    // a *variable* head (leading constants are eagerly consumed).  The per-variable
    // view groups (m_groups) are the "variable intersection membership constraints".
    struct cursor { unsigned i; expr* R; bool complete; };
    svector<cursor> m_cursors;              // one cursor per membership (parallel to m_atoms)
    unsigned        m_last_var = UINT_MAX;  // index (in m_vars) of the last expanded variable
    unsigned_vector m_head_cnt;
    unsigned_vector m_head_stack;

    // Brzozowski derivative of regex `r` by the concrete element `elem`.  Memoized on
    // (r, elem): the search revisits the same constant step on many branches.
    expr_ref der_elem(expr* r, expr* elem);

    // Memoized nullability of a derivative state: l_true / l_false / l_undef (unknown).
    lbool nullable(expr* r);

    // Symbolic transition cofactors in the selected mode.  The returned vector is owned
    // by seq_rewriter's mode-specific cofactor cache.
    expr_ref_pair_vector const& derivative_cofactors(expr* r);

    // Product-reachability emptiness of a conjunction of views (all on one
    // variable).  l_false = empty (unsat), l_true = non-empty (sat), l_undef = gave up
    // (cap overrun, non-range guard, or undecidable nullability).
    // On l_true, if `witness_word` is non-null it is set to a concrete sequence term
    // (over the element sort) whose value drives every view to acceptance
    // simultaneously -- i.e. a witness value for the variable the views constrain.
    lbool product_nonempty(seq::view_vector const& comps, expr_ref* witness_word = nullptr);

    // Flatten a str.++ term into atoms; false on an unsupported shape (non-constant unit).
    bool parse_term(expr* term, vector<atom>& atoms);

    // Rewrite re.reverse(r) away, giving a regex for the reversed language.  False when the
    // rewriter leaves a re.reverse behind, which it does for shapes it cannot push through
    // (a regex variable, an unexpanded derivative).  Reversing only some of the memberships
    // would put the system in a mixture of orientations, so a single failure makes prepare()
    // keep the whole problem forwards.
    bool reverse_regex(expr* r, expr_ref& result);

    // Wrap / unwrap the marker that names a variable's reversed reading.
    expr_ref mk_rev_var(expr* v);
    expr* strip_rev_var(expr* v) const;

    // Charge one search step against the budget and poll the global resource limit.
    // Returns true when the search must stop, having recorded the reason and set m_giveup.
    // One step is one product state or one dfs_atoms node, which is what the budget has
    // always counted; the loops that expand a single state are bounded separately (see
    // product_nonempty) so that this meaning stays intact.
    bool out_of_budget();

    // Run one decision in one direction with a given budget.  decide() layers the
    // orientation policy on top of this.
    lbool decide_oriented(membership_vec const& memberships, bool reversed, unsigned budget);

    unsigned work_bails() const { return m_stats.work_bails(); }

    // Drop all search state accumulated by the previous decide()/solve().
    void reset_search();

    // One pull of `iterator`: replay `resume` (when `has_resume`), then continue the
    // search from where that branch left off and report the next satisfying branch.
    lbool enumerate(membership_vec const& memberships, svector<choice> const& resume,
                    bool has_resume);

    // Abandon the search: the tree is not the one the replayed path was recorded on.
    lbool replay_bail();

    // Parse every membership into atoms, register its variables and count each
    // variable's occurrences.  Sets m_seq_sort/m_elem_sort.  False on an unsupported
    // shape, and on memberships over different sequence sorts.
    bool prepare(membership_vec const& memberships, bool reversed);

    bool group_complete(unsigned vi) const { return m_groups[vi].size() == m_num_occ[vi]; }

    // Index of `v` in m_vars / m_groups, registering it on first sight.
    unsigned var_index(expr* v);

    // Depth-first search over the monadic decomposition.  dfs_membership(mi) starts
    // membership `mi` (or reaches a leaf when every membership is consumed);
    // dfs_atoms(mi, i, R) continues membership `mi` at atom `i` with derivative state R.
    // l_true = a satisfying branch was found (recorded in m_solution), l_false = every
    // branch below is empty, l_undef = gave up.
    lbool dfs_membership(unsigned mi);
    lbool dfs_atoms(unsigned mi, unsigned i, expr* R);

    // ---- state-based search driver ----------------------------------------------------
    bool inc_budget();

    // One search step: pick the next variable to expand (preferring the last-expanded
    // variable, else the one occurring most often as a head atom of the active cursors),
    // and expand it.  Returns l_true (sat leaf found), l_false (this branch is empty), or
    // l_undef (gave up on a sub-branch).
    lbool search();

    // Expand variable `vi`, which is the head of the cursors in
    // m_head_stack[s_offset .. s_offset + s_size).  Assign a continuation (a reach target
    // q, or the epsilon/membership encoding for a last atom) to each cursor in turn (k
    // indexes the set), pushing the view on m_groups[vi] and pruning as soon as the
    // accumulated intersection for vi is empty.  When every cursor is assigned, recurse
    // into search().
    lbool choose_cont(unsigned vi, unsigned s_offset, unsigned s_size, unsigned k);

    lbool consume_constants(cursor& c, unsigned mi);

    // Advance cursor `mi` past its head variable to continuation `target` (null = the
    // variable is a last atom, i.e. a plain membership view), then eagerly consume
    // the following constant atoms.  l_false = the continuation is empty (prune),
    // l_undef = feasible but the tail nullability is unknown, l_true = feasible.
    lbool advance_cursor(cursor& c, unsigned mi, expr* target);

    // Emptiness of the views accumulated for variable `vi` on the current branch,
    // memoized on their signature.  Duplicates are collapsed before the product search
    // (they constrain the variable identically).
    lbool group_nonempty(unsigned vi);

    // All memberships consumed: every variable group has already been shown non-empty,
    // so this only records the branch as the solution.
    lbool leaf();

    // Decide a CONJUNCTION of memberships jointly (the core algorithm behind check()):
    // explores the joint decomposition of all memberships depth-first.  A variable shared
    // by several memberships accumulates several views in the same branch, which are
    // intersected -- enforcing one consistent value across all memberships.  Does not
    // touch m_memberships or m_core; fills m_solution on l_true.
    lbool decide(membership_vec const& memberships);

    // Given an unsatisfiable membership set, extract a minimal unsatisfiable subset by
    // deletion and collect the (non-null) dependencies of its members into m_core.
    void minimize_core(membership_vec const& memberships);

    bool is_var(expr *term) const {
        return m_is_var ? m_is_var(term) : is_uninterp(term);        
    }

public:
    seq_monadic(seq_rewriter& rw, trail_stack& undo_trail,
                seq::transition_mode mode = seq::transition_mode::light_antimirov_tm) :
        m(rw.m()), m_rw(rw), m_thrw(rw.m()), m_undo_trail(undo_trail),
        m_pin(rw.m()), m_config(mode), m_rp_cache(rw.m()), m_ivl_pin(rw.m()),
        m_regexes(rw.m()), m_live_states(rw, mode, 1u << 12), m_rev_decl(rw.m()) {}

    ~seq_monadic() { reset_ivl_cache(); }

    void collect_statistics(::statistics &st) const;

    // Display asserted constraints, result artifacts, search state, caches, and counters.
    std::ostream& display(std::ostream& out) const;

    seq::transition_mode mode() const { return m_config.m_mode; }

    // Record the solution (default: enabled).  Callers that only want the verdict
    // switch it off; the search itself is unaffected.
    void set_gen_solution(bool b) { m_config.m_solution = b; }
    bool gen_solution() const { return m_config.m_solution; }

    // Per variable, the views its value has to satisfy, from the last solve()/check()
    // that returned l_true.  The state/target terms stay valid until the next one.
    obj_map<expr, seq::view_vector> const& solution() const { return m_solution; }

    // Collapse `var`'s views into one value: a word driving all of them to acceptance
    // at once -- the first the product search finds, not the shortest.  The only place
    // a word gets built; its sort is taken from the views, resp. from `var` when the
    // search left it unconstrained.  l_true = `word` set, l_false = empty intersection,
    // l_undef = no recorded solution, or the search gave up.
    lbool materialize(expr* var, expr_ref& word);
    lbool materialize_all(expr_substitution& model);

    // Decide  (str.in_re term R)  for a term that is a concatenation of string variables
    // (possibly repeated / several distinct) and constant characters.
    //   l_true = sat, l_false = unsat, l_undef = unsupported shape / gave up.
    lbool solve(expr* term, expr* R);

    // Enable/disable unsat-core minimization (default: enabled).  When disabled, core()
    // returns the dependencies of all asserted memberships (no deletion-based shrinking).
    void set_min_core(bool b) { m_config.m_min_core = b; }

    void set_state_search(bool b) { m_config.m_state_search = b; }
    bool state_search() const { return m_config.m_state_search; }

    // Work budget consumed by a single solve()/check(): each search node and each product
    // expansion costs one unit, and the search gives up (l_undef, bail_reason::budget) when
    // it runs out.  The budget is reset per decision, so it bounds one decision rather than
    // the session.  A budget of 0 gives up immediately; UINT_MAX is effectively unbounded.
    void set_budget(unsigned b) { m_config.m_budget_limit = b; }

    unsigned budget() const { return m_config.m_budget_limit; }

    // Direction the search reads memberships in (default: forward).  Setting this to
    // `reversed` solves rev(term) in rev(R) instead, which is equisatisfiable and preserves
    // every length property; witnesses are reversed back before they are reported, so the
    // choice is not observable other than through the work it takes to reach an answer.
    void set_orientation(orientation o) { m_config.m_orientation = o; }

    orientation get_orientation() const { return m_config.m_orientation; }

    // Whether the last prepare() actually reversed the problem.  This can be false even
    // when the orientation is `reversed`, if some regex could not be reversed.
    bool is_reversed() const { return m_reversed; }

    void set_is_var(std::function<bool(expr *)> const &is_var) {
        m_is_var = is_var;
    }

    // Assert a membership  (term in regex)  to be decided jointly by the next check().
    // `d` carries the dependency used for unsat-core tracking and may be nullptr.
    // Memberships remain asserted until the constructor-provided trail is popped.
    void add(expr* term, expr* regex, void* d);

    // Replace the decided term of the membership carrying dependency `d` with `term`
    // (trailed, so the previous term is restored on pop).  Used to re-decide a membership
    // over the current expansion of its term once theory_seq's equalities define it as a
    // concatenation.  No-op if no membership carries `d`.
    void set_term(void* d, expr* term);

    // True if `term` is in the shape the solver can decide: a concatenation of string
    // constants, epsilon, seq.unit of constant elements, and sequence variables.  Callers
    // that rewrite a term before add()/set_term() (e.g. by expanding it through equalities)
    // can use this to avoid feeding a form that would only make check() bail.
    bool can_decide_term(expr* term);

    // Assert that `term` has at least `lo` elements.  A zero lower bound is a no-op.
    void add_lo(expr* term, unsigned lo, void* d);

    // Assert that `term` has at most `hi` elements.
    void add_hi(expr* term, unsigned hi, void* d);

    // Assert that `term` has exactly `len` elements.
    void add_len(expr* term, unsigned len, void* d);

    // Decide the CONJUNCTION of all memberships asserted via add() jointly: a variable
    // shared across memberships is constrained consistently (the DNFs are multiplied and
    // each variable's constraints intersected).  This is the natural extension of single-
    // membership solving to a Boolean combination of memberships (a disjunction is the
    // union of DNFs; a negated membership  ~(t in R)  is just  t in complement(R)).
    // Per-variable extra constraints are expressed as extra memberships (v in R').
    // Leaves the asserted memberships unchanged.  l_true = sat (empty conjunction is sat),
    // l_false = unsat, l_undef = gave up.  On l_false, core() holds the dependencies
    // of a minimal unsatisfiable subset.
    lbool check();

    // Dependencies of a minimal unsatisfiable subset from the last check() that returned
    // l_false (nullptr dependencies are omitted).  Empty otherwise.
    ptr_vector<void> const& core() const { return m_core; }

    // Lazy enumerator over the BRANCHES of the decomposition of a conjunction of
    // memberships: check() stops at the first satisfying branch, this hands them out one
    // at a time in the search's own order, so a caller can walk
    //
    //     conjunction  <=>  OR_i (branch i's per-variable views)
    //
    // as a lazy binary case split, the way seq_split::iterator is used for sigma.
    //
    // Suspension is by REPLAY: the iterator keeps its query and the choice path of the
    // branch it last reported, and a pull re-runs the search, descends that path and
    // continues from there.  It is therefore a plain value owning all it needs, and any
    // number of them survive being suspended across other uses of the engine (check()
    // probes, other iterators) -- which a search state living in the engine could not.
    //
    // next() returning false with gave_up() false means every branch not yet reported is
    // REFUTED, so the conjunction holds only if a reported branch does.  gave_up() (a
    // budget / state cap, an undecidable nullability, a replay mismatch, the emission
    // limit, or the positional driver, which records no choices) means the enumeration is
    // incomplete and its end proves nothing.
    class iterator {
        seq_monadic&    m_engine;
        membership_vec  m_memberships;   // own copy: the query is re-prepared per pull
        svector<choice> m_path;          // choice path of the last reported branch
        expr_ref_vector m_path_pin;      // keeps that path's states alive across pulls
        unsigned        m_limit;         // cap on the number of branches reported
        unsigned        m_count = 0;
        bool            m_started = false;
        bool            m_done = false;
        bool            m_giveup = false;
    public:
        iterator(seq_monadic& engine, membership_vec const& memberships, unsigned limit);
        // Report the next branch as the views it commits each variable to; fills
        // `solution` on success, and keeps returning false once it has returned it.
        bool next(obj_map<expr, seq::view_vector>& solution);
        bool gave_up() const { return m_giveup; }
        unsigned count() const { return m_count; }
    };

    // Enumerate the branches of the conjunction of all memberships asserted via add().
    // The iterator snapshots them, so it outlives the trail scope they were asserted in.
    // `limit` caps the branches reported; hitting it is a give-up, not an exhaustion.
    iterator iterate(unsigned limit);
};
