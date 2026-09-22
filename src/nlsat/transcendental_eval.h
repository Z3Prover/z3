/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    transcendental_eval.h

Abstract:

    Shared floating point evaluation, conservative round-off error bounds,
    and exact rational Taylor/Maclaurin bracket routines for transcendental
    functions (sin, cos, tan, exp, log, ...).

    This is pure numeric math with no dependency on either solver engine's
    control logic. It lives in nlsat (rather than a neutral location) since
    nlsat is the lower layer both engines already depend on: it is used by
    nlsat::transcendentals (nlsat_transcendentals.cpp, the exact
    axiom/refinement engine nlsat runs when nra_solver delegates to it) and
    by nla::transcendentals (math/lp/nla_transcendentals.cpp, the cheap
    per-node delta-consistency filter nla_core runs on every check(), which
    already depends on the nlsat component via nra_solver.cpp), so that the
    numeric core the two engines rely on cannot silently drift apart. The
    two engines still differ in *when* and *how* they invoke this math and
    in how they turn a detected inconsistency into a lemma/clause -- that
    control logic intentionally remains separate.

Author:

    Nikolaj Bjorner

--*/
#pragma once
#include "util/rational.h"

namespace nlsat {
namespace transcendental_eval {

    enum class op_kind {
        SIN, COS, TAN, ASIN, ACOS, ATAN, SINH, COSH, TANH, ASINH, ACOSH, ATANH, EXP, LOG
    };

    char const* op_name(op_kind op);

    // Evaluates op at x in double precision. NaN/+-inf results (e.g. asin
    // outside [-1,1], log of a negative number) are expected for
    // out-of-domain arguments; callers are responsible for handling them
    // (typically via std::isfinite checks).
    double eval(op_kind op, double x);

    // A conservative (not tight) additive error bound accounting for the
    // floating point round-off incurred by evaluating op in double
    // precision at x with result fx. Functions whose derivative can blow
    // up near the boundary of their domain (tan's poles, asin/acos/atanh
    // near +-1, acosh near 1, log near 0) get a larger safety margin than
    // the everywhere-smooth, bounded-derivative ones (sin, cos, tanh,
    // asinh).
    double error_bound(op_kind op, double x, double fx);

    // Exact rational equal to the finite double d, obtained from d's binary
    // (mantissa, exponent) representation via frexp/ldexp: this never loses
    // precision (unlike scaling by a power of ten), so no outward-rounding
    // slack needs to be reserved for the conversion itself.
    rational to_rational(double d);

    // A (non-certified) floating point enclosure of op over the box
    // [lo, hi]: samples op at both endpoints, then inflates the resulting
    // range by error_bound so that small deviations from monotonicity
    // within the (intentionally tiny) box are covered as well. Always
    // succeeds (assumes op is finite/monotone-ish across the tiny box).
    void interval_eval(op_kind op, double lo, double hi, double& lo_val, double& hi_val);

    // A wider-box-aware floating point enclosure of op over [lo, hi]:
    // like interval_eval, but also accounts for a periodic extremum
    // (e.g. sin's peak at pi/2) or pole (tan) falling inside [lo, hi]
    // rather than assuming the endpoints alone bound the range. Returns
    // false if lo > hi, an endpoint is non-finite, or a pole is found
    // strictly inside the box (the caller should fall back to
    // interval_eval on a tiny box instead).
    bool wide_interval_eval(op_kind op, double lo, double hi, double& lo_val, double& hi_val);

    // Exact rational Maclaurin bracket [lo, hi] for exp(x) at a single
    // point x: for x <= 0 the series sum x^n/n! is alternating once
    // n+1 >= |x| (skipping a possibly non-monotone initial run of terms
    // before that), so consecutive partial sums bracket the value from
    // there on; for x > 0 all terms are positive (a sound, monotonically
    // increasing lower bound), and the omitted tail is bounded by a
    // geometric series for the upper bound.
    bool exp_taylor_bracket_at(rational const& xr, rational& lo, rational& hi);

    // Exact rational Mercator (Taylor-at-1) bracket [lo, hi] for log(x),
    // valid only for 1 <= x <= 2: writing u = x-1 in [0,1], log(1+u) is a
    // genuine alternating series there, so consecutive partial sums
    // bracket the true value from the very first term.
    bool log_taylor_bracket_at(rational const& xr, rational& lo, rational& hi);

    // Exact rational Maclaurin bracket [lo, hi] for atan(x), valid only
    // for |x| <= 1 (the series' radius of convergence): atan(x) =
    // x - x^3/3 + x^5/5 - ... is a genuine alternating series there, so
    // consecutive partial sums bracket the true value.
    bool atan_taylor_bracket_at(rational const& xr, rational& lo, rational& hi);

}
}
