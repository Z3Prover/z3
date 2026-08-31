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
            bool       m_has_sup = false;    // an upper bound was proven: no model has obj >= sup, m_sup_upper >= sup
            rational   m_sup_upper;
            model_ref  m_model;              // best model
            unsigned   m_rounds = 0;
            result(ast_manager& m): m_value(m) {}
            void reset();
        };

        nlsat_opt(ast_manager& m, params_ref const& p);

        /**
           \brief Maximize obj subject to the hard constraints and lo <= obj (<= hi when provided).
           Returns l_true when the optimum is proven (r.m_attained),
           l_undef when the problem is outside nlsat's fragment or the round
           budget is exhausted (r.m_model, if set, is the best model found),
           and l_false when hard /\ lo <= obj <= hi has no model.
        */
        lbool maximize(expr_ref_vector const& hard, expr* obj, rational const& lo, std::optional<rational> const& hi,
                       unsigned max_rounds, result& r);

    private:
        // The steps of maximize, in order.
        lbool preprocess(expr_ref_vector const& hard, expr* obj, rational const& lo, std::optional<rational> const& hi,
                         app_ref& T, goal_ref& pg);
        bool load(goal const& pg, app* T, nlsat::solver& s, nlsat::var& t, expr_ref_vector& x2t, expr_ref_vector& b2a);
        model_ref extract_model(nlsat::solver& s, expr_ref_vector const& x2t, expr_ref_vector const& b2a, app* T,
                                model_converter* mc);
        void set_result(algebraic_numbers::manager& am, algebraic_numbers::anum const& best, bool attained, result& res);
    };
}
