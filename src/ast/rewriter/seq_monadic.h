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
    of conjunctions of per-variable *components*:

      - reach component    <var, state0, q>       : the variable's value drives the
                                                     derivative automaton from state0 to q
      - membership component<var, state0, null>    : the variable's value is in L(state0)

    That disjunction is NEVER materialized as a DNF.  Materializing it costs the product
    of the per-position split degrees (and, for a conjunction of memberships, the product
    over memberships), which is the dominant cost in practice.  Instead the decomposition
    is explored as a depth-first search tree: one branch at a time, components pushed on
    entry and popped on backtracking.  A variable's accumulated components are tested for
    emptiness as soon as the search passes the variable's LAST occurrence -- the test has
    to be done anyway, and doing it there prunes the whole remaining subtree.  The search
    stops at the first satisfying leaf.

    reach(q) is therefore NEVER built as a regex (which state-elimination would blow up
    super-polynomially for lattice-shaped automata).  Instead the constraints on a
    variable are decided directly by a lazy product-reachability search over tuples of
    component states: a product state accepts iff every reach component is at its target
    and every membership component is nullable; transitions are the product of the
    components' cofactor branches with pairwise-conjoined range guards (minterm-free).
    This stays in the product-of-state-counts regime, never the path-enumeration (k!)
    regime of regex state-elimination.

    Supports single / multiple / repeated variables.  Per-variable extra constraints
    (e.g. a base membership intersected with a length-regex) are expressed as an extra
    membership passed to `add` and decided by `check`.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
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

    struct config {
        seq::transition_mode m_mode;
        bool m_model = true;  // whether solve()/check() extract a feasible model

        config(seq::transition_mode mode) : m_mode(mode) {}
    };

    enum class bail_reason { unsupported, state_cap, dnf_cap, budget, resource, nullability, guard, num_reasons };

    struct statistics {
        unsigned m_cofactor_calls = 0;
        unsigned m_states = 0;
        unsigned m_bails[static_cast<unsigned>(bail_reason::num_reasons)] = {};

        void inc_bail(bail_reason reason) {
            ++m_bails[static_cast<unsigned>(reason)];
        }
    };

    ast_manager&    m;
    seq_rewriter&   m_rw;
    th_rewriter     m_thrw;                  // normalizes constant-element derivatives (folds
                                             // ground guards so dead states become re.empty)
    trail_stack&    m_undo_trail;
    sort*           m_seq_sort = nullptr;   // sequence sort of the regex under analysis
    sort*           m_elem_sort = nullptr;  // element sort of that sequence sort
    expr_ref_vector m_pin;                  // pins derivative states / witnesses referenced later
    unsigned        m_budget = 0;           // global work budget (search nodes + product pops)
    bool            m_giveup = false;       // set when the budget is exhausted
    config          m_config;
    statistics      m_stats;
    obj_map<expr, expr*> m_model;           // last extracted model (var -> witness); see get_model()
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
    ptr_vector<void> m_core;                // dependencies of an unsat subset, filled by check()/solve() on l_false
    ptr_vector<void> m_core_trail;          // deps collected inline as branches close during decide();
                                            // shrunk on a satisfiable/undetermined branch, kept on a refuted one
    std::function<bool(expr *)> m_is_var;   // predicate for whether a term is a sequence variable
    lbool m_last_result = l_undef;           // result of the last public solve()/check()
    lbool m_last_search_result = l_undef;    // result of the last internal decide()

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

    // A component of one variable's constraint.  As the variable's value w is read,
    // the current state is derived from `state`; the component accepts when
    //   target ? (current == target)      -- reach component (w drives A from state to target)
    //           : nullable(current)        -- membership component (w in L(state))
    // `dep` is the dependency of the membership that produced this component; it is
    // collected into the unsat core when the variable's component intersection is empty.
    struct component { expr* var; expr* state; expr* target; void* dep; };

    // ---- depth-first search state; valid for the duration of one decide()/solve() ----
    vector<vector<atom>>   m_atoms;         // parsed atoms, one entry per membership
    expr_ref_vector        m_regexes;       // regex of each membership (parallel to m_atoms)
    ptr_vector<void>       m_deps;          // dependency of each membership (parallel to m_atoms)
    ptr_vector<expr>       m_vars;          // variables occurring in the memberships
    obj_map<expr, unsigned> m_var_idx;      // variable -> index into m_vars / m_groups
    vector<svector<component>> m_groups;    // components accumulated on the current branch
    obj_map<expr, uint64_t> m_last_occ;     // variable -> last (membership, atom) position
    unsigned               m_undef_vars = 0;  // depth of groups whose emptiness test gave up
    // memo for the per-variable emptiness test, keyed by the sorted, deduplicated
    // (state, target) signature of the variable's component group
    typedef std::vector<std::pair<unsigned, unsigned>> group_sig;
    struct group_sig_hash {
        size_t operator()(group_sig const& s) const {
            size_t h = 1469598103934665603ull;
            for (auto const& p : s) {
                h = (h ^ p.first) * 1099511628211ull;
                h = (h ^ p.second) * 1099511628211ull;
            }
            return h;
        }
    };
    group_sig m_sig_buf;                    // reused by group_nonempty (avoids allocating per lookup)
    std::unordered_map<group_sig, lbool, group_sig_hash> m_group_cache;
    seq::live_states m_live_states;

    // Brzozowski derivative of regex `r` by the concrete element `elem`.  Memoized on
    // (r, elem): the search revisits the same constant step on many branches.
    expr_ref der_elem(expr* r, expr* elem);

    // Memoized nullability of a derivative state: l_true / l_false / l_undef (unknown).
    lbool nullable(expr* r);

    // Symbolic transition cofactors in the selected mode.  The returned vector is owned
    // by seq_rewriter's mode-specific cofactor cache.
    expr_ref_pair_vector const& derivative_cofactors(expr* r);

    // Product-reachability emptiness of a conjunction of components (all on one
    // variable).  l_false = empty (unsat), l_true = non-empty (sat), l_undef = gave up
    // (cap overrun, non-range guard, or undecidable nullability).
    // On l_true, if `witness_word` is non-null it is set to a concrete sequence term
    // (over the element sort) whose value drives every component to acceptance
    // simultaneously -- i.e. a witness value for the variable the components constrain.
    lbool product_nonempty(svector<component> const& comps, expr_ref* witness_word = nullptr);

    // Flatten a str.++ term into atoms; false on an unsupported shape (non-constant unit).
    bool parse_term(expr* term, vector<atom>& atoms);

    // Drop all search state accumulated by the previous decide()/solve().
    void reset_search();

    // Parse every membership into atoms, register its variables and record each
    // variable's last occurrence.  Sets m_seq_sort/m_elem_sort.  False on an
    // unsupported shape.
    bool prepare(membership_vec const& memberships);

    // Index of `v` in m_vars / m_groups, registering it on first sight.
    unsigned var_index(expr* v);

    // Depth-first search over the monadic decomposition.  dfs_membership(mi) starts
    // membership `mi` (or reaches a leaf when every membership is consumed);
    // dfs_atoms(mi, i, R) continues membership `mi` at atom `i` with derivative state R.
    // l_true = a satisfying branch was found (m_model is filled when model generation is
    // enabled), l_false = every branch below is empty, l_undef = gave up.
    //
    // The public entry points are thin wrappers enforcing the core-collection discipline:
    // each remembers the m_core_trail height on entry and, on a non-refuting result
    // (l_true / l_undef), rewinds the trail to that height -- so only deps pushed on the
    // committed refutation subtree survive.  The *_body methods hold the actual search.
    lbool dfs_membership(unsigned mi);
    lbool dfs_atoms(unsigned mi, unsigned i, expr* R);
    lbool dfs_membership_body(unsigned mi);
    lbool dfs_atoms_body(unsigned mi, unsigned i, expr* R);

    // Push the dependency `d` (if non-null) onto the core trail.
    void push_dep(void* d) { if (d) m_core_trail.push_back(d); }
    // Push the dependencies of every component currently accumulated for variable `vi`;
    // used when that variable's component intersection is found empty (a closed branch).
    void push_group_deps(unsigned vi) {
        for (auto const& c : m_groups[vi])
            push_dep(c.dep);
    }
    // Deduplicate m_core_trail into m_core after a l_false decide().
    void finalize_core();

    // Emptiness of the components accumulated for variable `vi` on the current branch,
    // memoized on their signature.  Duplicated components are collapsed before the
    // product search (they constrain the variable identically).
    lbool group_nonempty(unsigned vi);

    // All memberships consumed: every variable group has already been shown non-empty,
    // so this only extracts witnesses when model generation is enabled.
    lbool leaf();

    // Decide a CONJUNCTION of memberships jointly (the core algorithm behind check()):
    // explores the joint decomposition of all memberships depth-first.  A variable shared
    // by several memberships accumulates several components in the same branch, which are
    // intersected -- enforcing one consistent value across all memberships.  Does not
    // touch m_memberships; fills m_model on l_true when model generation is enabled and,
    // on l_false, leaves the dependencies that closed the search in m_core_trail.
    lbool decide(membership_vec const& memberships);

    bool is_var(expr *term) const {
        return m_is_var ? m_is_var(term) : is_uninterp(term);        
    }

public:
    seq_monadic(seq_rewriter& rw, trail_stack& undo_trail,
                seq::transition_mode mode = seq::transition_mode::light_antimirov_tm) :
        m(rw.m()), m_rw(rw), m_thrw(rw.m()), m_undo_trail(undo_trail),
        m_pin(rw.m()), m_config(mode), m_rp_cache(rw.m()), m_ivl_pin(rw.m()),
        m_regexes(rw.m()), m_live_states(rw, mode, 1u << 12) {}

    ~seq_monadic() { reset_ivl_cache(); }

    void collect_statistics(::statistics &st) const;

    // Display asserted constraints, result artifacts, search state, caches, and counters.
    std::ostream& display(std::ostream& out) const;

    seq::transition_mode mode() const { return m_config.m_mode; }

    // Enable/disable model generation (default: enabled).  When enabled, a successful
    // solve()/check() extracts a feasible model retrievable via get_model().
    void set_gen_model(bool b) { m_config.m_model = b; }

    // The model extracted by the last successful solve()/check(): var -> witness,
    // where each witness is a concrete sequence term (over the element sort) giving one
    // satisfying assignment.  Witness terms are pinned by the solver and remain valid
    // until the next solve()/check().  Only valid when model generation is enabled.
    obj_map<expr, expr*> const& get_model() const { return m_model; }

    // Decide  (str.in_re term R)  for a term that is a concatenation of string variables
    // (possibly repeated / several distinct) and constant characters.
    //   l_true = sat, l_false = unsat, l_undef = unsupported shape / gave up.
    lbool solve(expr* term, expr* R);

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
    // of an unsatisfiable subset (the union of the deps that closed the refuted branches).
    lbool check();

    // Dependencies of an unsatisfiable subset from the last check() that returned
    // l_false (nullptr dependencies are omitted).  Empty otherwise.
    ptr_vector<void> const& core() const { return m_core; }
};
