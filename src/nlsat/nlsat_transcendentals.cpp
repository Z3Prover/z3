/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nlsat_transcendentals.cpp

Abstract:

    See nlsat_transcendentals.h.

Author:

    Nikolaj Bjorner

--*/
#include "nlsat/nlsat_transcendentals.h"
#include "nlsat/nlsat_solver.h"
#include "math/polynomial/polynomial.h"
#include "math/polynomial/algebraic_numbers.h"
#include <cmath>
#include <limits>

namespace nlsat {

    double transcendentals::eval(transcendental_op_kind op, double x) {
        switch (op) {
        case transcendental_op_kind::SIN:  return std::sin(x);
        case transcendental_op_kind::COS:  return std::cos(x);
        case transcendental_op_kind::EXP:  return std::exp(x);
        case transcendental_op_kind::ATAN: return std::atan(x);
        }
        return std::numeric_limits<double>::quiet_NaN();
    }

    // Same conservative (not tight) round-off margin as
    // nla::transcendentals::error_bound (math/lp/nla_transcendentals.cpp):
    // a generous constant times machine epsilon, scaled by the argument (for
    // the bounded-derivative sin/cos/atan) or by the function value (for
    // exp, whose derivative is unbounded but grows with the value itself).
    double transcendentals::error_bound(transcendental_op_kind op, double x, double fx) {
        double const eps = std::numeric_limits<double>::epsilon();
        double const safety = 64.0; // generous margin, this is not a tight certificate
        switch (op) {
        case transcendental_op_kind::SIN:
        case transcendental_op_kind::COS:
        case transcendental_op_kind::ATAN:
            return safety * eps * std::max(1.0, std::fabs(x));
        case transcendental_op_kind::EXP:
            return safety * eps * std::max(1.0, std::fabs(fx));
        }
        return 1e-6;
    }

    // Exact rational equal to the finite double d (see
    // nla::transcendentals::to_rational for the same construction): obtained
    // from d's binary (mantissa, exponent) representation via frexp/ldexp,
    // so no precision is lost and no outward-rounding slack is needed for
    // the conversion itself.
    rational transcendentals::to_rational(double d) {
        if (d == 0.0)
            return rational(0);
        int exp = 0;
        double mantissa = std::frexp(d, &exp); // d = mantissa * 2^exp, 0.5 <= |mantissa| < 1
        int64_t num = static_cast<int64_t>(std::ldexp(mantissa, 53));
        exp -= 53;
        rational r(num);
        if (exp >= 0)
            r *= rational::power_of_two(static_cast<unsigned>(exp));
        else
            r /= rational::power_of_two(static_cast<unsigned>(-exp));
        return r;
    }

    // true if some integer k has lo <= phase + k*period <= hi.
    static bool contains_multiple_of(double lo, double hi, double phase, double period) {
        if (!(lo <= hi))
            return false;
        double k = std::ceil((lo - phase) / period);
        double candidate = phase + k * period;
        return candidate <= hi;
    }

    bool transcendentals::interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val) {
        if (!(lo <= hi))
            return false;
        double f_lo = eval(op, lo);
        double f_hi = eval(op, hi);
        if (!std::isfinite(f_lo) || !std::isfinite(f_hi))
            return false;
        double mn = std::min(f_lo, f_hi);
        double mx = std::max(f_lo, f_hi);
        double const pi = 3.14159265358979323846;
        double const two_pi = 2 * pi;
        switch (op) {
        case transcendental_op_kind::SIN:
            if (contains_multiple_of(lo, hi, pi / 2, two_pi)) mx = 1.0;
            if (contains_multiple_of(lo, hi, -pi / 2, two_pi)) mn = -1.0;
            break;
        case transcendental_op_kind::COS:
            if (contains_multiple_of(lo, hi, 0.0, two_pi)) mx = 1.0;
            if (contains_multiple_of(lo, hi, pi, two_pi)) mn = -1.0;
            break;
        default:
            break; // EXP, ATAN: monotonic increasing everywhere, endpoints give the range.
        }
        double slack = std::max(error_bound(op, lo, f_lo), error_bound(op, hi, f_hi));
        lo_val = mn - slack;
        hi_val = mx + slack;
        return true;
    }

    // Builds the literal x < bound (k == LT) or x > bound (k == GT), clearing
    // bound's denominator first since polynomial::manager coefficients must
    // be integers (mirrors nra_solver::add_transcendental_axioms' scaling).
    static literal bound_literal(solver& s, var x, atom::kind k, rational const& bound) {
        rational den = denominator(bound);
        rational coeff = den;
        rational c = -(bound * den);
        polynomial_ref p(s.pm().mk_linear(1, &coeff, &x, c), s.pm());
        poly* pp = p.get();
        bool is_even = false;
        return s.mk_ineq_literal(k, 1, &pp, &is_even);
    }

    bool transcendentals::refine_app(app const& a) {
        rational l, u;
        // A rational witness (the common case: nlsat's own model
        // construction favors rational values whenever nothing forces an
        // irrational root) yields l == u exactly; an irrational witness
        // yields a genuine isolating interval - either way the enclosure
        // below is computed uniformly from [l, u].
        s.am().get_interval(s.value(a.arg), l, u, 64);
        // Widen the (possibly zero-width) interval a little before
        // sampling: without this, a rational witness reduces refine_app to
        // a point-exclusion lemma, which only forbids nlsat from proposing
        // that exact value again - not values arbitrarily close to it. That
        // is sound but can make the search stall on repeated near-identical
        // lemmas when the true solution sits at (or converges toward) a
        // fixed point, exactly the slow-convergence failure mode fixed for
        // nla::transcendentals's own Taylor-bracket lemmas (see
        // nla_transcendentals.cpp's taylor_exclusion_delta /
        // widen_unit_derivative_bound). interval_eval's endpoint sampling
        // (with the SIN/COS extremum check) stays sound for any width, so
        // widening here carries none of the soundness risk that widening a
        // *conflicting* bound required guarding against there.
        double mid = (l.get_double() + u.get_double()) / 2.0;
        double delta = 1e-6 * std::max(1.0, std::fabs(mid));
        double lo_d = l.get_double() - delta;
        double hi_d = u.get_double() + delta;
        double lo_val, hi_val;
        if (!interval_eval(a.op, lo_d, hi_d, lo_val, hi_val)) {
            // Fall back to the unwidened (or, failing that, the plain
            // point) interval; l <= u always holds by construction of
            // get_interval, so this call cannot fail.
            if (!interval_eval(a.op, l.get_double(), u.get_double(), lo_val, hi_val))
                return false;
            lo_d = l.get_double();
            hi_d = u.get_double();
        }
        rational rlo = to_rational(lo_val), rhi = to_rational(hi_val);
        anum const& yv = s.value(a.val);
        if (s.am().ge(yv, rlo.to_mpq()) && s.am().le(yv, rhi.to_mpq()))
            return false; // already consistent with the enclosure.

        rational xlo = to_rational(lo_d), xhi = to_rational(hi_d);
        literal_vector lemma;
        lemma.push_back(bound_literal(s, a.arg, atom::LT, xlo));
        lemma.push_back(bound_literal(s, a.arg, atom::GT, xhi));
        if (s.am().lt(yv, rlo.to_mpq()))
            lemma.push_back(~bound_literal(s, a.val, atom::LT, rlo)); // val >= rlo
        else
            lemma.push_back(~bound_literal(s, a.val, atom::GT, rhi)); // val <= rhi
        s.mk_clause(lemma.size(), lemma.data(), nullptr);
        return true;
    }

    bool transcendentals::refine() {
        bool added = false;
        for (auto const& a : m_apps)
            if (refine_app(a))
                added = true;
        return added;
    }
}
