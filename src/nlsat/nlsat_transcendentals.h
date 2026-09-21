/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nlsat_transcendentals.h

Abstract:

    Direct-in-nlsat handling of transcendental function applications
    (sin/cos/tan/asin/acos/atan/sinh/cosh/tanh/asinh/acosh/atanh/exp/log).

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

    nra_solver always registers transcendental applications directly with
    nlsat (see nra_solver::imp::register_transcendentals_with_nlsat), so this
    module's refinement loop is the sole engine used to solve them; there is
    no longer an alternative nla_core-side Taylor-axiom-injection path.

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

    enum class transcendental_op_kind {
        SIN, COS, TAN, ASIN, ACOS, ATAN, SINH, COSH, TANH, ASINH, ACOSH, ATANH, EXP, LOG
    };

    class transcendentals {
    public:
        struct app {
            transcendental_op_kind op;
            var arg;
            var val;
        };

        // A pair of output variables of two applications that share the
        // same (structural) argument variable, related by an exact
        // polynomial identity (see add_identity_axioms): (sin_val, cos_val),
        // (cosh_val, sinh_val), (cosh_val, tanh_val).
        struct identity_pair {
            var v1;
            var v2;
        };

        // A registered application of the binary function atan2(y, x), val
        // meant to represent atan2(y, x) (range (-pi, pi]). Kept separate
        // from app above since y and x play structurally different roles
        // (y's sign alone fixes val's sign; x's sign alone selects the
        // branch) - ported from nla::transcendentals::atan2_app /
        // add_atan2 / check_atan2 (math/lp/nla_transcendentals.*).
        struct atan2_app {
            var y;
            var x;
            var val;
        };

    private:
        solver&      s;
        vector<app>  m_apps;
        // Pairs discovered so far (see add()); asserted immediately as
        // permanent polynomial equality axioms the moment the second
        // application of a matching pair is registered - see
        // add_identity_axiom.
        vector<identity_pair> m_sin_cos_pairs;
        vector<identity_pair> m_cosh_sinh_pairs;
        vector<identity_pair> m_cosh_tanh_pairs;
        // Registered atan2(y, x) applications; see atan2_app and add_atan2.
        vector<atan2_app> m_atan2_apps;
        // The var nlsat was given for the nullary constant pi, if any
        // (null_var otherwise); see add_pi. Ported from
        // nla::transcendentals::pi_var / m_pi_var.
        var m_pi_var = null_var;
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
        // Same widening-retry counter as m_retry, indexed in lockstep with
        // m_atan2_apps instead of m_apps.
        unsigned_vector m_retry_atan2;

        static double eval(transcendental_op_kind op, double x);
        static double error_bound(transcendental_op_kind op, double x, double fx);
        static rational to_rational(double d);

        // Conservative floating point enclosure of op over [lo, hi] (lo may
        // equal hi): endpoint sampling inflated by error_bound, with SIN/COS
        // additionally checking whether a local extremum (a multiple of
        // pi/2) falls inside the interval, COSH checking whether its
        // minimum (at 0) falls inside it, and TAN bailing out (returning
        // false) if a pole falls strictly inside it - EXP, LOG, ATAN, ASIN,
        // ACOS, SINH, TANH, ASINH, ACOSH, ATANH are all monotonic
        // increasing (or, for ACOS, decreasing) everywhere on their domain,
        // so plain endpoint sampling already gives a sound range for them.
        // Returns false (no enclosure produced) if an endpoint evaluates to
        // a non-finite double, or a TAN pole falls inside [lo, hi].
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

        // Exact, unconditional value-range bound, ported from
        // nla::transcendentals::add_range_axioms: -1<=sin,cos<=1;
        // -1<tanh<1; cosh>=1; acosh>=0; -pi/2<=asin<=pi/2; 0<=acos<=pi
        // (pi/2, pi rounded outward - see k_pi_2_ub/k_pi_ub in the .cpp).
        // Added once, permanently, the moment the application is
        // registered (add()), same as add_global_axioms above. TAN, SINH,
        // ASINH, ATANH have no simple unconditional bound and are skipped.
        void add_range_axioms(transcendental_op_kind op, var val);

        // Exact cross-application identity axiom, ported from
        // nla::transcendentals's module comment / add_transcendental:
        // sin(t)^2+cos(t)^2=1, cosh(t)^2-sinh(t)^2=1,
        // cosh(t)^2*(1-tanh(t)^2)=1. Scans previously-registered
        // applications for one with the same argument variable and a
        // complementary op, and - if found - asserts the corresponding
        // permanent polynomial equality the moment the second application
        // of the pair is registered.
        void find_and_add_identity_axiom(transcendental_op_kind op, var arg, var val);
        void add_identity_axiom(identity_pair const& pr, bool is_sin_cos, bool is_cosh_sinh);

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

        // atan2(y, x): the exact fact sign(val) == sign(y) whenever y != 0,
        // asserted as a lemma when violated; then a float-based check
        // against std::atan2(y, x) with a coarse case-split fallback on
        // sign(x) - ported from nla::transcendentals::check_atan2.
        bool refine_atan2(unsigned idx);

    public:
        explicit transcendentals(solver& s): s(s) {}

        bool empty() const { return m_apps.empty() && m_atan2_apps.empty(); }
        void add(transcendental_op_kind op, var arg, var val);

        // Registers the var nlsat was given for the nullary constant pi:
        // asserts the same tight, exact-rational two-sided bound as
        // nla::transcendentals::add_pi, and remembers it so other checks
        // (none yet in this module) can refer to pi directly. A no-op if
        // val is null_var or pi has already been registered.
        void add_pi(var val);

        // Registers a binary atan2(y, x) application: y and x are the two
        // input vars, val the output. Asserts atan2's permanent range
        // axiom (-pi <= val <= pi) and records the application for
        // refine() (see refine_atan2). A no-op if any of y, x, val is
        // null_var. Ported from nla::transcendentals::add_atan2.
        void add_atan2(var y, var x, var val);

        // null_var if add_pi has not (yet) been called.
        var pi_var() const { return m_pi_var; }

        // Remaps every var stored directly in this module's own bookkeeping
        // (m_apps/m_atan2_apps/m_pi_var - none of which live inside a
        // polynomial, so solver::reorder's m_pm.rename() does not touch
        // them) according to permutation p (p[old_var] == new_var), exactly
        // like solver::reorder already does for m_bounds. Must be called
        // from solver::reorder whenever variables get physically permuted,
        // otherwise these stale indices silently point at the wrong
        // variable after the first reorder.
        void rename(unsigned sz, var const* p) {
            for (app& a : m_apps) {
                if (a.arg < sz) a.arg = p[a.arg];
                if (a.val < sz) a.val = p[a.val];
            }
            for (atan2_app& a : m_atan2_apps) {
                if (a.y < sz) a.y = p[a.y];
                if (a.x < sz) a.x = p[a.x];
                if (a.val < sz) a.val = p[a.val];
            }
            auto rename_pairs = [&](vector<identity_pair>& pairs) {
                for (identity_pair& ip : pairs) {
                    if (ip.v1 < sz) ip.v1 = p[ip.v1];
                    if (ip.v2 < sz) ip.v2 = p[ip.v2];
                }
            };
            rename_pairs(m_sin_cos_pairs);
            rename_pairs(m_cosh_sinh_pairs);
            rename_pairs(m_cosh_tanh_pairs);
            if (m_pi_var != null_var && m_pi_var < sz)
                m_pi_var = p[m_pi_var];
        }

        void reset() { m_apps.reset(); m_retry.reset(); m_sin_cos_pairs.reset(); m_cosh_sinh_pairs.reset(); m_cosh_tanh_pairs.reset(); m_atan2_apps.reset(); m_retry_atan2.reset(); m_pi_var = null_var; }

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
