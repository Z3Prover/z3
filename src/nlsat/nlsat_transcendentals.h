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

    The per-application reasoning (exact global tangent-line bounds, exact
    rational Taylor/Maclaurin sandwiches, and cross-application
    monotonicity) is ported from nla::transcendentals
    (math/lp/nla_transcendentals.*), adapted to this module's simpler flat
    application list and to nlsat's own polynomial/literal API in place of
    nla_core's lar_term/lemma_builder.

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
        // Per-application retry counter, indexed in lockstep with m_apps:
        // incremented every time refine_app excludes an interval around the
        // current witness for that application, so repeated near-identical
        // witnesses (e.g. nlsat converging toward a tangent point where the
        // function's value touches a global axiom bound) get an
        // exponentially widening exclusion instead of the same tiny
        // fixed-epsilon one every round - without this, convergence toward
        // such a point can take arbitrarily many refinement rounds (each
        // only ruling out an infinitesimally small neighborhood).
        unsigned_vector m_retry;

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

        // Exact rational Taylor/Maclaurin brackets [lo, hi] at a single
        // point xr, ported from nla::transcendentals
        // (math/lp/nla_transcendentals.cpp's exp_taylor_bracket_at /
        // log_taylor_bracket_at / check_atan_taylor_range): unlike
        // interval_eval above, these carry no floating point round-off
        // risk at all - lo/hi are genuine rational bounds derived from an
        // alternating (EXP for x<=0, LOG, ATAN) or monotonically increasing
        // (EXP for x>0, via a geometric tail bound) series, so [lo, hi] is
        // guaranteed (not just probably, up to float slack) to contain
        // op(xr). Each returns false outside the domain where the
        // respective series argument is applicable; refine_app falls back
        // to interval_eval there.
        static bool exp_taylor_bracket_at(rational const& xr, rational& lo, rational& hi);
        static bool log_taylor_bracket_at(rational const& xr, rational& lo, rational& hi);
        static bool atan_taylor_bracket_at(rational const& xr, rational& lo, rational& hi);

        // Registers the exact global tangent-line axioms (sound for the
        // op's *entire* domain, not just a local neighborhood of some
        // witness) ported from nla::transcendentals::check_exp_lower_bound
        // / check_log_upper_bound: exp(arg) >= 1+arg unconditionally, and
        // arg <= 0 \/ log(arg) <= arg-1. Added once, as permanent clauses,
        // the moment the application is registered (add()) rather than
        // reactively in refine(), since - unlike the Taylor sandwich, whose
        // bounds are only valid near a specific witness - these hold
        // everywhere and can only help pruning sooner.
        void add_global_axioms(transcendental_op_kind op, var arg, var val);

        // Cross-application monotonicity, ported from
        // nla::transcendentals::check_exp_monotonicity /
        // check_log_monotonicity: x1 < x2 => op(x1) < op(x2) for every pair
        // of registered EXP (unconditional) or LOG (both args positive)
        // applications. Unlike add_global_axioms this is witness-dependent
        // (only a violated pair yields a lemma) so it is checked from
        // refine(), alongside the per-application Taylor/interval check.
        bool refine_monotonicity();
        bool refine_monotonicity_pair(app const& a, app const& b);

        bool refine_app(unsigned idx);

    public:
        explicit transcendentals(solver& s): s(s) {}

        bool empty() const { return m_apps.empty(); }
        void add(transcendental_op_kind op, var arg, var val);
        void reset() { m_apps.reset(); m_retry.reset(); }

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
