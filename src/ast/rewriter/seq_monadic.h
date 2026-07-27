/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.h

Abstract:

    Whole-language monadic decomposition for regex membership of a term that is a
    concatenation of string variables and constant characters, e.g.  x.a.x in R.

    Self-contained decision procedure: NO Nielsen splitting (seq_split), NO minterms,
    and NO materialization of reach(q) as a regex.  It relies only on the symbolic
    Brzozowski derivative (brz_derivative_cofactors as a transition regex) and on
    automaton product-reachability for emptiness.

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

    Supports single / multiple / repeated variables, and per-variable extra constraints
    (base membership + length-regex) via `var_extra`.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_range_predicate.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"

class seq_monadic {
    ast_manager&    m;
    seq_rewriter&   m_rw;
    sort*           m_seq_sort = nullptr;   // sequence sort of the regex under analysis
    expr_ref_vector m_pin;                  // pins derivative states referenced by components
    unsigned        m_budget = 0;           // global work budget (decompose disjuncts + product pops)
    bool            m_giveup = false;       // set when the budget is exhausted

    seq_util&      u() const { return m_rw.u(); }
    seq_util::rex& re() const { return m_rw.u().re; }

    // A term atom: a string variable or a constant character.
    struct atom { bool is_var; expr* var; unsigned ch; };

    // A component of one variable's constraint.  As the variable's value w is read,
    // the current state is derived from `state`; the component accepts when
    //   target ? (current == target)      -- reach component (w drives A from state to target)
    //           : nullable(current)        -- membership component (w in L(state))
    struct component { expr* var; expr* state; expr* target; };

    typedef svector<component> disjunct;    // a conjunction of components (a DNF disjunct)

    // Brzozowski derivative of regex `r` by the concrete character `ch`.
    expr_ref der_char(expr* r, unsigned ch);

    // Live reachable derivative states of R (BFS over cofactor targets + liveness
    // least-fixpoint).  These are the split states q.  Sets `ok` false on a cap overrun.
    void live_states(expr* R, ptr_vector<expr>& out, bool& ok);

    // Product-reachability emptiness of a conjunction of components (all on one
    // variable).  l_false = empty (unsat), l_true = non-empty (sat), l_undef = gave up
    // (cap overrun, non-range guard, or undecidable nullability).
    lbool product_nonempty(svector<component> const& comps);

    // Flatten a str.++ term into atoms; false on an unsupported shape (non-constant unit).
    bool parse_term(expr* term, svector<atom>& atoms, expr*& the_var);

    // Monadic decomposition: append to `out` the DNF disjuncts for  atoms[i..] in R,
    // threading the current derivative state R.  `ok` false on give-up.
    void decompose(svector<atom> const& atoms, unsigned i, expr* R,
                   vector<disjunct>& out, bool& ok);

    // Drop disjuncts with a syntactically-empty component and dedup identical disjuncts.
    void simplify_dnf(vector<disjunct>& dnf);

public:
    seq_monadic(seq_rewriter& rw) : m(rw.m()), m_rw(rw), m_pin(rw.m()) {}

    // Decide  (str.in_re term R)  for a term that is a concatenation of string variables
    // (possibly repeated / several distinct) and constant characters.
    //   l_true = sat, l_false = unsat, l_undef = unsupported shape / gave up.
    lbool solve(expr* term, expr* R);

    // As above, with extra per-variable constraints (e.g. a base membership intersected
    // with a length-regex): `var_extra` maps a variable to a regex it must also satisfy.
    lbool solve(expr* term, expr* R, obj_map<expr, expr*> const& var_extra);
};
