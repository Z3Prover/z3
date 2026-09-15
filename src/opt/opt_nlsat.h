/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_nlsat.h

Abstract:

    Exact optimization of a real-valued objective over quantifier-free
    nonlinear real arithmetic using nlsat cells.

    The objective is bound to a fresh variable t that is placed first in
    nlsat's variable order. t is always assigned the largest value that its
    current feasible set allows - an endpoint of a cell, in general an
    algebraic number. Every model found is blocked by the constraint
    t > value (a root atom when the value is irrational) until the problem
    becomes unsatisfiable, which proves the last value optimal
    (GOMT F-Sat / F-Close over nlsat cells).

    For a finite open limit, combine a refutation of t >= limit with a
    budgeted nlqsat query showing that feasible values approach the limit
    from below. The returned model remains a feasible point below the limit.

Author:

    Lev Nachmanson 2026-08-25

--*/
#pragma once

#include <optional>
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "model/model.h"
#include "nlsat/nlsat_types.h"
#include "tactic/goal.h"
#include "util/params.h"
#include "util/lbool.h"

namespace algebraic_numbers { class manager; class anum; }
namespace nlsat { class solver; }
class model_converter;

namespace opt {

    /**
       \brief True when the hard constraints and obj lie in the fragment
       nlsat decides: Boolean structure over polynomial arithmetic atoms,
       with uninterpreted constants as the only free symbols.
    */
    bool in_nra_fragment(ast_manager& m, arith_util& a, expr_ref_vector const& hard, expr* obj);

    // Express equality to a real numeral using rational-coefficient constraints,
    // so both the SMT arithmetic solver and nlqsat can use an algebraic value.
    expr_ref mk_algebraic_eq(ast_manager& m, expr* term, expr* value);

    class nlsat_opt {
        ast_manager&  m;
        params_ref    m_params;
        arith_util    m_arith;
    public:
        struct result {
            expr_ref   m_value;              // exact value of the best model (a numeral, possibly algebraic); null if none
            rational   m_lower;              // rational bracket of m_value: m_lower <= m_value <= m_upper
            rational   m_upper;
            bool       m_attained = false;   // m_value is proven optimal
            bool       m_unbounded = false;  // the objective is proven unbounded above; m_value/m_model are only a witness
            bool       m_has_sup = false;    // m_sup is a proven strict upper bound, not necessarily the least one
            bool       m_open = false;       // m_sup is also approachable from below: a certified unattained supremum
            expr_ref   m_sup;
            rational   m_sup_lower;          // rational bracket of m_sup, independent of the best model's bracket
            rational   m_sup_upper;
            model_ref  m_model;              // best model
            unsigned   m_rounds = 0;
            result(ast_manager& m): m_value(m), m_sup(m) {}
            void reset();
        };

        nlsat_opt(ast_manager& m, params_ref const& p);

        /**
           \brief Maximize obj subject to the hard constraints and lo <= obj (<= hi when provided).
           Returns l_true when a verdict is proven: the optimum (r.m_attained),
           a finite unattained supremum (r.m_open), or, with no upper bound
           given, unboundedness (r.m_unbounded);
           l_undef when the problem is outside nlsat's fragment or the round
           budget is exhausted (r.m_model, if set, is the best model found),
           and l_false when hard /\ lo <= obj <= hi has no model.
           supremum_rlimit bounds the extra finite-limit certification query;
           zero disables that query without disabling upper-bound checks.
        */
        lbool maximize(expr_ref_vector const& hard, expr* obj, rational const& lo, std::optional<rational> const& hi,
                       unsigned max_rounds, result& r, unsigned supremum_rlimit = 100000);

        /**
           \brief Check whether feasible objective values approach bound from below:
           forall e > 0. exists xs. hard /\ lo <= obj /\ bound-e < obj < bound.
           bound must be an arithmetic numeral, possibly algebraic.
           This alone does not prove that bound is an upper bound. Maximize
           separately refutes obj >= bound before accepting an open supremum.
           Returns l_undef outside the real-arithmetic fragment or when the
           query exceeds rlimit_budget; zero disables the query.
        */
        lbool can_approach_from_below(expr_ref_vector const& hard, expr* obj, rational const& lo,
                                     expr* bound, unsigned rlimit_budget = 100000);

        /**
           \brief Decide whether obj is unbounded above over the hard
           constraints and lo <= obj (lo must be attained by some model):
           one quantified-NRA (nlqsat) query on the closed statement
           (forall c. exists xs. hard /\ lo <= obj /\ obj > c). Returns
           l_true (unbounded above), l_false (some upper bound exists, value
           not computed), l_undef (outside the fragment or the solver gave up).
        */
        lbool prove_unbounded(expr_ref_vector const& hard, expr* obj, rational const& lo);

    private:
        lbool prove_unbounded(goal const& pg, app* T);
        lbool can_approach_from_below(goal const& pg, app* T, expr* bound);
        void prove_strict_upper_bound(nlsat::solver& s, nlsat::var t, algebraic_numbers::anum const& sup,
                                      algebraic_numbers::anum const& best, result& res);
        // The steps of maximize, in order.
        lbool preprocess(expr_ref_vector const& hard, expr* obj, rational const& lo, std::optional<rational> const& hi,
                         app_ref& T, goal_ref& pg);
        bool load(goal const& pg, app* T, nlsat::solver& s, nlsat::var& t, expr_ref_vector& x2t, expr_ref_vector& b2a);
        model_ref extract_model(nlsat::solver& s, expr_ref_vector const& x2t, expr_ref_vector const& b2a, app* T,
                                model_converter* mc);
        void set_value(algebraic_numbers::manager& am, algebraic_numbers::anum const& value,
                       expr_ref& numeral, rational& lower, rational& upper);
    };
}
