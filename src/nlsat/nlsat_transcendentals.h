/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nlsat_transcendentals.h

Abstract:

    Direct-in-nlsat handling of transcendental function applications
    (sin/cos/exp/atan/log).

    This is an alternative to nla::transcendentals (math/lp/nla_transcendentals.*):
    that module grows Taylor-sandwich polynomial axioms *outside* nlsat and
    re-invokes nlsat as a fresh, one-shot solver every time it wants to give
    nlsat a tighter approximation (nra_solver::check() calls reset(), which
    reallocates the whole nlsat::solver instance). Growing and re-solving from
    scratch is sound but throws away all of nlsat's incremental search state
    (learned clauses, variable order, watch lists, ...) on every refinement
    round.

    This module instead keeps a persistent nlsat::solver instance in charge
    and refines the model *inside* nlsat's own search loop
    (solver::imp::search_check), exactly where integer branch-and-bound
    already tightens variable bounds and re-runs search() without tearing
    down the solver: refine() is called right after search() reports l_true,
    checks every registered application's current witness against a
    conservative floating point enclosure of the function (see eval /
    error_bound below), and - if some application's value is inconsistent -
    adds a permanent interval-exclusion clause and signals the caller to
    re-run search().

    Use smt_params_helper's arith.nl.transcendental_engine to select which of
    the two implementations nla_core delegates to.

Author:

    Nikolaj Bjorner

--*/
#pragma once

#include "nlsat/nlsat_types.h"
#include "util/vector.h"
#include "util/rational.h"

namespace nlsat {

    class solver;

    enum class transcendental_op_kind { SIN, COS, EXP, ATAN, LOG };

    class transcendentals {
    public:
        struct app {
            transcendental_op_kind op;
            var arg;
            var val;
        };

    private:
        solver&      s;
        vector<app>  m_apps;

        static double eval(transcendental_op_kind op, double x);
        static double error_bound(transcendental_op_kind op, double x, double fx);
        static rational to_rational(double d);

        // Conservative floating point enclosure of op over [lo, hi] (lo may
        // equal hi): endpoint sampling inflated by error_bound, with SIN/COS
        // additionally checking whether a local extremum (a multiple of
        // pi/2) falls inside the interval - EXP and ATAN are monotonic
        // increasing everywhere, so plain endpoint sampling already gives a
        // sound range for them. Returns false (no enclosure produced) only
        // if an endpoint evaluates to a non-finite double.
        static bool interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val);

        bool refine_app(app const& a);

    public:
        explicit transcendentals(solver& s): s(s) {}

        bool empty() const { return m_apps.empty(); }
        void add(transcendental_op_kind op, var arg, var val) { m_apps.push_back({ op, arg, val }); }
        void reset() { m_apps.reset(); }

        // Called right after search() reports l_true, mirroring the integer
        // branch-and-bound check in solver::imp::search_check. Adds a
        // permanent clause and returns true for every registered
        // application whose current witness violates its floating point
        // enclosure; the caller should re-initialize the search and try
        // again (as with branch and bound). Returns false without adding
        // any clause if the model is already consistent with every
        // registered application.
        bool refine();
    };
}
