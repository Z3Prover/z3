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
    variable splits again, the last variable is a plain membership) yields a DNF whose
    disjuncts are conjunctions of per-variable *components*:

      - reach component    <var, state0, q>       : the variable's value drives the
                                                     derivative automaton from state0 to q
      - membership component<var, state0, null>    : the variable's value is in L(state0)

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
#include "ast/rewriter/guard_set.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/dependency.h"
#include "util/trail.h"
#include <utility>
#include <tuple>

class seq_monadic {
public:
    enum class transition_mode {
        brzozowski,
        light_antimirov
    };

private:
    // Self-contained memo for derivative_cofactors: maps a regex to its (owned) cofactor
    // vector and keeps a trail of pinned keys so they stay live for the cache's lifetime.
    // The memoized cofactors depend only on the regex (and the fixed transition mode), so
    // the cache is valid across solve()/decide()/check() calls; callers reset it only when
    // it grows past a size cap (maybe_reset).
    class cofactor_cache {
        obj_map<expr, expr_ref_pair_vector*>  m_cache;
        expr_ref_vector                       m_pin;      // trail of pinned keys
    public:
        cofactor_cache(ast_manager& m) : m_pin(m) {}
        ~cofactor_cache() { reset(); }
        bool find(expr* r, expr_ref_pair_vector*& v) const { return m_cache.find(r, v); }
        void insert(expr* r, expr_ref_pair_vector* v) { m_pin.push_back(r); m_cache.insert(r, v); }
        unsigned size() const { return m_cache.size(); }
        void reset() {
            for (auto const& [k, v] : m_cache)
                dealloc(v);
            m_cache.reset();
            m_pin.reset();
        }
        void maybe_reset(unsigned cap) { if (m_cache.size() > cap) reset(); }
    };

    struct config {
        transition_mode m_mode;
        bool m_model = true;  // whether solve()/check() extract a feasible model
        bool m_min_core = true;   // whether check() minimizes the unsat core (else: all deps)

        config(transition_mode mode) : m_mode(mode) {}
    };

    ast_manager&    m;
    seq_rewriter&   m_rw;
    th_rewriter     m_thrw;                  // normalizes constant-element derivatives (folds
                                             // ground guards so dead states become re.empty)
    trail_stack&    m_undo_trail;
    sort*           m_seq_sort = nullptr;   // sequence sort of the regex under analysis
    sort*           m_elem_sort = nullptr;  // element sort of that sequence sort
    expr_ref_vector m_pin;                  // pins derivative states / witnesses referenced later
    unsigned        m_budget = 0;           // global work budget (decompose disjuncts + product pops)
    bool            m_giveup = false;       // set when the budget is exhausted
    config          m_config;
    statistics      m_stats;
    obj_map<expr, expr*> m_model;           // last extracted model (var -> witness); see get_model()
    cofactor_cache  m_cofactors;            // memoizes derivative_cofactors per regex (see class above)
    guard_set::cache m_rp_cache;             // cofactor guard -> range predicate
    using membership_vec = vector<std::tuple<expr_ref, expr_ref, void*>>;
    membership_vec m_memberships;           // asserted (term in regex, dep) for check()
    ptr_vector<void> m_core;                // dependencies of an unsat subset, filled by check() on l_false
    std::function<bool(expr *)> m_is_var;   // predicate for whether a term is a sequence variable

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
    struct component { expr* var; expr* state; expr* target; };

    typedef svector<component> disjunct;    // a conjunction of components (a DNF disjunct)

    // Brzozowski derivative of regex `r` by the concrete element `elem`.
    expr_ref der_elem(expr* r, expr* elem);

    // Symbolic transition cofactors in the selected mode.  Memoized per regex `r` in
    // m_cofactors: the returned vector is owned by that cache (see the cofactor_cache
    // class above for the persistence/reset policy).
    expr_ref_pair_vector const& derivative_cofactors(expr* r);

    // Live reachable derivative states of R (BFS over cofactor targets + liveness
    // least-fixpoint).  These are the split states q.  Returns false on a cap overrun.
    bool live_states(expr* R, expr_ref_vector& out);

    // Product-reachability emptiness of a conjunction of components (all on one
    // variable).  l_false = empty (unsat), l_true = non-empty (sat), l_undef = gave up
    // (cap overrun, non-range guard, or undecidable nullability).
    // On l_true, if `witness_word` is non-null it is set to a concrete sequence term
    // (over the element sort) whose value drives every component to acceptance
    // simultaneously -- i.e. a witness value for the variable the components constrain.
    lbool product_nonempty(svector<component> const& comps, expr_ref* witness_word = nullptr);

    // Flatten a str.++ term into atoms; false on an unsupported shape (non-constant unit).
    bool parse_term(expr* term, vector<atom>& atoms, expr*& the_var);

    // Monadic decomposition: append to `out` the DNF disjuncts for  atoms[i..] in R,
    // threading the current derivative state R.  Returns false on give-up.
    bool decompose(vector<atom> const& atoms, unsigned i, expr* R,
                   vector<disjunct>& out);

    // Drop disjuncts with a syntactically-empty component and dedup identical disjuncts.
    void simplify_dnf(vector<disjunct>& dnf);

    // Build the DNF over primitive per-variable components for one membership term in R.
    // Sets m_seq_sort/m_elem_sort; false on an unsupported shape or give-up.
    bool build_membership_dnf(expr* term, expr* R, vector<disjunct>& dnf);

    // Decide a DNF (over primitive components): sat iff some disjunct has every variable
    // group non-empty.  On l_true, when model generation is enabled, fills m_model
    // (var -> witness).
    lbool decide_dnf(vector<disjunct> const& dnf);

    // Decide a CONJUNCTION of memberships jointly (the core algorithm behind check()):
    // multiplies the per-membership DNFs and decides emptiness.  Does not touch
    // m_memberships or m_core; fills m_model on l_true when model generation is enabled.
    lbool decide(membership_vec const& memberships);

    // Given an unsatisfiable membership set, extract a minimal unsatisfiable subset by
    // deletion and collect the (non-null) dependencies of its members into m_core.
    void minimize_core(membership_vec const& memberships);

    bool is_var(expr *term) const {
        return m_is_var ? m_is_var(term) : is_uninterp(term);        
    }

public:
    seq_monadic(seq_rewriter& rw, trail_stack& undo_trail,
                transition_mode mode = transition_mode::light_antimirov) :
        m(rw.m()), m_rw(rw), m_thrw(rw.m()), m_undo_trail(undo_trail),
        m_pin(rw.m()), m_config(mode), m_cofactors(rw.m()), m_rp_cache(rw.m()) {}

    ~seq_monadic() = default;

    transition_mode mode() const { return m_config.m_mode; }

    void collect_statistics(::statistics& st) const;

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

    // Enable/disable unsat-core minimization (default: enabled).  When disabled, core()
    // returns the dependencies of all asserted memberships (no deletion-based shrinking).
    void set_min_core(bool b) { m_config.m_min_core = b; }

    void set_is_var(std::function<bool(expr *)> const &is_var) {
        m_is_var = is_var;
    }

    // Assert a membership  (term in regex)  to be decided jointly by the next check().
    // `d` carries the dependency used for unsat-core tracking and may be nullptr.
    // Memberships remain asserted until the constructor-provided trail is popped.
    void add(expr* term, expr* regex, void* d);

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
};
