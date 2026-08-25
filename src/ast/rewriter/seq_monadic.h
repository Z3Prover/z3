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
        unsigned m_budget_limit = 1000000;  // value m_budget is reset to on each decide()
        orientation m_orientation = orientation::forward;
        // Refinement rounds allowed when decomposing an intersection of regexes; 0 = off.
        unsigned m_split_rounds = 0;

        config(seq::transition_mode mode) : m_mode(mode) {}
    };

    // `stale`: an `iterator` was resumed after another search took the engine's stack away,
    // so it can no longer report the branches it still owed.  A caller that suspends an
    // iterator across unrelated engine calls will see this and must fall back conservatively.
    enum class bail_reason { unsupported, state_cap, budget, state_expansion, resource, nullability, guard, not_reversible, stale, num_reasons };

    struct statistics {
        unsigned m_cofactor_calls = 0;
        unsigned m_states = 0;
        unsigned m_max_state_expansion = 0;  // most inner steps any single product state took
        unsigned m_split_calls = 0;          // decisions handed to the intersection split
        unsigned m_split_rounds = 0;         // refinement rounds spent across those decisions
        unsigned m_split_decided = 0;        // ... that the split then decided
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
    expr_ref_vector m_pin;                  // pins derivative states / witnesses referenced later
    unsigned        m_budget = 0;           // global work budget (search nodes + product pops)
    bool            m_giveup = false;       // set when the budget is exhausted
    config          m_config;
    statistics      m_stats;
    obj_map<expr, seq::view_vector> m_solution;  // var -> views, from the last decide()
    obj_map<expr, expr*> m_split_words;     // var -> witness word, cached per refinement round
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

    membership_vec m_memberships;           // asserted (term in regex, dep) for check()
    membership_vec m_last_search_memberships; // inputs used by the last internal decide()
    ptr_vector<void> m_core;                // dependencies of an unsat subset, filled by check() on l_false
    std::function<bool(expr *)> m_is_var;   // predicate for whether a term is a sequence variable
    lbool m_last_result = l_undef;           // result of the last public solve()/check()
    lbool m_last_search_result = l_undef;    // result of the last internal decide()
    bool m_reversed = false;                 // whether prepare() reversed the current problem
    bool m_retry_disabled = false;           // reversed retry gave up once on this query
    bool m_split_disabled = false;           // suppresses decide()'s intersection decomposition
                                             // while an unsat core is being minimized

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
    obj_map<expr, uint64_t> m_last_occ;     // variable -> last (membership, atom) position
    unsigned               m_undef_vars = 0;  // depth of groups whose emptiness test gave up

    // ---- the branch, as an explicit stack ------------------------------------------
    // The search runs on its own stack rather than on the C++ one, so a branch can be left
    // standing and picked up again later (see the public `iterator`).  Only VARIABLE atoms
    // branch, so one frame per variable atom is the whole branch, and everything a frame
    // has to undo on backtracking sits in the frame.
    struct frame {
        unsigned mi, i;      // the variable atom this frame stands on ...
        expr*    R;          // ... and the derivative state there: the view's source state
        unsigned vi;         // index of that variable in m_vars / m_groups
        bool     finalize;   // last occurrence of vi, so its group test is forced here
        bool     last_atom;  // the variable ends its membership: a plain membership view
        unsigned next = 0;       // next live state of R to try (the forced case tries one)
        bool     undef = false;  // whether this frame's view is one m_undef_vars counts
    };
    svector<frame> m_stack;
    unsigned m_pos_mi = 0;      // position the next frame will be pushed at: membership,
    unsigned m_pos_i = 0;       // atom, and the derivative state there
    expr*    m_pos_R = nullptr;
    bool m_any_undef = false;   // a branch was passed over undecided, so running the tree
                                // to its end no longer refutes anything
    unsigned m_search_gen = 0;  // bumped per search: an `iterator` from an older one has
                                // had its stack thrown away and says so instead of resuming
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
    lbool product_nonempty(expr* var, seq::view_vector const& comps, expr_ref* witness_word = nullptr);

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
    // One step is one product state or one node of the decomposition tree, which is what
    // the budget has always counted; the loops that expand a single state are bounded
    // separately (see product_nonempty) so that this meaning stays intact.
    bool out_of_budget();

    // Run one decision in one direction with a given budget.  decide() layers the
    // orientation policy on top of this.
    lbool decide_oriented(membership_vec const& memberships, bool reversed, unsigned budget);

    unsigned work_bails() const { return m_stats.work_bails(); }

    // Drop all search state accumulated by the previous decide()/solve().
    void reset_search();

    // One pull of `iterator`: run the search to its next satisfying branch, from scratch
    // or on from the branch it stands on.
    lbool enumerate(membership_vec const& memberships, bool resume);

    // Parse every membership into atoms, register its variables and record each
    // variable's last occurrence.  False on an
    // unsupported shape, and on memberships over different sequence sorts.
    bool prepare(membership_vec const& memberships, bool reversed);

    // Index of `v` in m_vars / m_groups, registering it on first sight.
    unsigned var_index(expr* v);

    // ---- depth-first search over the monadic decomposition ---------------------------

    void start_membership(unsigned mi);

    // Run the position forward over the forced steps -- a constant atom consumed by a
    // derivative, the end of a membership by a nullability test -- stopping at the next
    // variable atom or at the leaf.  l_undef abandons the branch.
    lbool advance_pos();

    // Push a frame for the variable atom the position stands on.  False at the leaf.
    bool push_frame();

    // Give `f` its next continuation and run the position on past it, skipping the ones
    // the accumulated intersection for f.vi refutes.  False once none is left.
    bool commit_next(frame& f);

    // Run the search up to the next accepting leaf.  `resume` picks it up at the leaf it
    // stands on and continues as if that leaf had failed.  l_false = tree exhausted.
    lbool run_search(bool resume);

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

    // One pass of the orientation policy over `memberships` with an explicit budget.
    // `sticky` allows a failed reversed retry to disable retrying for the rest of the
    // query -- appropriate only for an attempt that was given the full budget.
    lbool decide_policy(membership_vec const& memberships, unsigned budget, bool sticky);

    // ---- decomposition of intersections of regexes -------------------------------------
    // A membership t in R1 & ... & Rk makes the search explore the product of all k regexes
    // at once.  These decide instead a RELAXATION that keeps only some of the Ri, and grow
    // it on demand.  Dropping intersected regexes only enlarges the language, so a
    // relaxation that is unsatisfiable refutes the original, and a model that every dropped
    // Ri accepts satisfies it.  Anything else falls back to the undecomposed search.

    // The conjuncts of a membership: the arguments of its top-level intersection, flattened
    // through nested re.inter.  A membership that is not an intersection yields itself.
    void split_conjuncts(expr* r, ptr_vector<expr>& out);

    // Whether `r` restricts the lengths of the words it accepts to a proper subset of a
    // residue class, i.e. contains a loop with equal bounds above 1.
    bool constrains_length(expr* r);

    // Replace the variables of `term` by the values the recorded solution collapses to,
    // appending the resulting concrete elements to `elems`.  False if some part has no
    // value or is not a word.
    bool instantiate_word(expr* term, ptr_vector<expr>& elems, bool subst = true);

    // Whether the recorded solution makes `term` a member of `r`, by deriving r along the
    // instantiated word.  l_undef when the word or a derivative cannot be evaluated.
    lbool model_accepts(expr* term, expr* r);

    // materialize() without its precondition on the last top-level result, so that the
    // refinement loop can read the solution of a search it ran itself.
    lbool materialize_recorded(expr* var, expr_ref& word);

    // Decide `memberships` by refining a relaxation of their intersections, for at most
    // m_split_rounds rounds and `allowance` units of work in total.  l_undef leaves the
    // caller no worse off than before.
    lbool decide_split(membership_vec const& memberships, unsigned budget, unsigned allowance);

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

    // Refinement rounds allowed for decomposing a membership in an intersection of regexes,
    // once both reading directions have run out of budget.  0 (the default) disables it, so
    // the search behaves exactly as before.
    void set_split_rounds(unsigned n) { m_config.m_split_rounds = n; }

    unsigned split_rounds() const { return m_config.m_split_rounds; }

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
    // at a time, so a caller can walk
    //
    //     conjunction  <=>  OR_i (branch i's per-variable views)
    //
    // as a lazy case split instead of materializing the disjunction.
    //
    // The search state is the engine's, so exactly ONE iterator can be in flight: anybody
    // else's solve()/check() takes the stack away, and the iterator then gives up rather
    // than resuming.
    //
    // next() returning false with gave_up() false means every branch not yet reported is
    // REFUTED, so the conjunction holds only if a reported branch does.  gave_up() means
    // the enumeration is incomplete and its end proves nothing.
    class iterator {
        seq_monadic&    m_engine;
        membership_vec  m_memberships;   // own copy: outlives the scope it was asserted in
        unsigned        m_limit;         // cap on the number of branches reported
        unsigned        m_count = 0;
        unsigned        m_gen = 0;       // engine search this iterator's stack belongs to
        bool            m_started = false;
        bool            m_done = false;
        bool            m_giveup = false;
    public:
        iterator(seq_monadic& engine, membership_vec const& memberships, unsigned limit);
        // Report the next branch as the views it commits each variable to.  While it
        // holds, materialize() collapses those views to concrete words.
        bool next(obj_map<expr, seq::view_vector>& solution);
        bool gave_up() const { return m_giveup; }
        unsigned count() const { return m_count; }
    };

    // Enumerate the branches of the conjunction of all memberships asserted via add().
    // The iterator snapshots them, so it outlives the trail scope they were asserted in.
    // `limit` caps the branches reported; hitting it is a give-up, not an exhaustion.
    iterator iterate(unsigned limit);
};
