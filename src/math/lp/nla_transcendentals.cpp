/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

  nla_transcendentals.cpp

Author:
  Nikolaj Bjorner (nbjorner)

Description:

  See nla_transcendentals.h

--*/
#include <cmath>
#include <limits>
#include "math/lp/nla_core.h"
#include "math/lp/nla_transcendentals.h"

namespace nla {

    void transcendentals::add_transcendental(transcendental_op_kind op, lpvar arg, lpvar val) {
        if (arg == null_lpvar || val == null_lpvar)
            return;
        m_apps.push_back({ op, arg, val });
        m_core.trail().push(push_back_vector(m_apps));
        add_range_axioms(op, val);
    }

    // pi/2 and pi, each rounded outward (away from the true value) by more
    // than double's rounding error, so that using them as bounds never
    // excludes a value the corresponding function can actually attain.
    static constexpr double k_pi_2_ub = 1.5707963267948968; // > true pi/2
    static constexpr double k_pi_ub   = 3.1415926535897936; // > true pi

    void transcendentals::add_range_axioms(transcendental_op_kind op, lpvar val) {
        auto& lra = m_core.lra;
        switch (op) {
        case transcendental_op_kind::SIN:
        case transcendental_op_kind::COS:
            lra.add_var_bound(val, lp::lconstraint_kind::LE, rational(1));
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(-1));
            break;
        case transcendental_op_kind::TANH:
            lra.add_var_bound(val, lp::lconstraint_kind::LT, rational(1));
            lra.add_var_bound(val, lp::lconstraint_kind::GT, rational(-1));
            break;
        case transcendental_op_kind::COSH:
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(1));
            break;
        case transcendental_op_kind::ACOSH:
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(0));
            break;
        case transcendental_op_kind::ASIN:
            lra.add_var_bound(val, lp::lconstraint_kind::LE, to_rational(k_pi_2_ub));
            lra.add_var_bound(val, lp::lconstraint_kind::GE, to_rational(-k_pi_2_ub));
            break;
        case transcendental_op_kind::ATAN:
            lra.add_var_bound(val, lp::lconstraint_kind::LT, to_rational(k_pi_2_ub));
            lra.add_var_bound(val, lp::lconstraint_kind::GT, to_rational(-k_pi_2_ub));
            break;
        case transcendental_op_kind::ACOS:
            lra.add_var_bound(val, lp::lconstraint_kind::LE, to_rational(k_pi_ub));
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(0));
            break;
        default:
            break; // TAN, SINH, ASINH, ATANH: no simple unconditional bound.
        }
    }

    char const* transcendentals::op_name(transcendental_op_kind op) {
        switch (op) {
        case transcendental_op_kind::SIN:   return "sin";
        case transcendental_op_kind::COS:   return "cos";
        case transcendental_op_kind::TAN:   return "tan";
        case transcendental_op_kind::ASIN:  return "asin";
        case transcendental_op_kind::ACOS:  return "acos";
        case transcendental_op_kind::ATAN:  return "atan";
        case transcendental_op_kind::SINH:  return "sinh";
        case transcendental_op_kind::COSH:  return "cosh";
        case transcendental_op_kind::TANH:  return "tanh";
        case transcendental_op_kind::ASINH: return "asinh";
        case transcendental_op_kind::ACOSH: return "acosh";
        case transcendental_op_kind::ATANH: return "atanh";
        }
        return "?";
    }

    double transcendentals::eval(transcendental_op_kind op, double x) {
        switch (op) {
        case transcendental_op_kind::SIN:   return std::sin(x);
        case transcendental_op_kind::COS:   return std::cos(x);
        case transcendental_op_kind::TAN:   return std::tan(x);
        // std::asin/std::acos return NaN outside [-1,1]; OP_U_ASIN/OP_U_ACOS
        // are the separate operators z3 uses for that out-of-domain case, so
        // NaN here is expected and handled by the isfinite check below.
        case transcendental_op_kind::ASIN:  return std::asin(x);
        case transcendental_op_kind::ACOS:  return std::acos(x);
        case transcendental_op_kind::ATAN:  return std::atan(x);
        case transcendental_op_kind::SINH:  return std::sinh(x);
        case transcendental_op_kind::COSH:  return std::cosh(x);
        case transcendental_op_kind::TANH:  return std::tanh(x);
        case transcendental_op_kind::ASINH: return std::asinh(x);
        case transcendental_op_kind::ACOSH: return std::acosh(x); // NaN for x < 1
        case transcendental_op_kind::ATANH: return std::atanh(x); // NaN/+-inf for |x| >= 1
        }
        return std::numeric_limits<double>::quiet_NaN();
    }

    // A conservative (not tight) additive error bound accounting for the
    // floating point round-off incurred by evaluating op in double
    // precision. It does not attempt to bound the error of converting an
    // exact rational argument to a double in the first place; that
    // rounding is itself included in the same margin for simplicity.
    // Functions whose derivative can blow up near the boundary of their
    // domain (tan's poles, asin/acos/atanh near +-1, acosh near 1) get a
    // larger safety margin than the everywhere-smooth, bounded-derivative
    // ones (sin, cos, tanh, asinh).
    double transcendentals::error_bound(transcendental_op_kind op, double x, double fx) {
        double const eps = std::numeric_limits<double>::epsilon();
        double const safety = 64.0;       // generous margin, this is not a tight certificate
        double const boundary_safety = 4096.0; // extra margin near domain boundaries/poles
        switch (op) {
        case transcendental_op_kind::SIN:
        case transcendental_op_kind::COS:
        case transcendental_op_kind::TANH:
        case transcendental_op_kind::ASINH:
            return safety * eps * std::max(1.0, std::fabs(x));
        case transcendental_op_kind::SINH:
        case transcendental_op_kind::COSH:
            return safety * eps * std::max(1.0, std::fabs(fx));
        case transcendental_op_kind::TAN:
        case transcendental_op_kind::ASIN:
        case transcendental_op_kind::ACOS:
        case transcendental_op_kind::ATANH:
        case transcendental_op_kind::ACOSH:
            return boundary_safety * eps * std::max(1.0, std::max(std::fabs(x), std::fabs(fx)));
        case transcendental_op_kind::ATAN:
            return safety * eps * std::max(1.0, std::fabs(x));
        }
        return 1e-6;
    }

    // Exact rational equal to the finite double d, obtained from d's binary
    // (mantissa, exponent) representation via frexp/ldexp: this never loses
    // precision (unlike scaling by a power of ten), so no outward-rounding
    // slack needs to be reserved for the conversion itself.
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

    // A (non-certified) floating point enclosure of op over the box [lo,
    // hi]: samples op at both endpoints, then inflates the resulting range
    // by error_bound so that small deviations from monotonicity within the
    // (intentionally tiny) box are covered as well.
    void transcendentals::interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val) {
        double f_lo = eval(op, lo);
        double f_hi = eval(op, hi);
        double lo_v = std::min(f_lo, f_hi);
        double hi_v = std::max(f_lo, f_hi);
        double slack = std::max(error_bound(op, lo, f_lo), error_bound(op, hi, f_hi));
        lo_val = lo_v - slack;
        hi_val = hi_v + slack;
    }

    // true if some integer k has lo <= phase + k*period <= hi (used to
    // detect whether a periodic function's extremum/pole falls inside
    // [lo, hi]). A generous (safe) direction: false negatives would be
    // unsound (missing an extremum), but this can only produce false
    // positives (from floating point slack in the endpoint comparison),
    // which merely widens an already-sound enclosure or triggers an
    // unnecessary fallback - never unsound.
    static bool contains_multiple_of(double lo, double hi, double phase, double period) {
        if (!(lo <= hi))
            return false;
        double k = std::ceil((lo - phase) / period);
        double candidate = phase + k * period;
        return candidate <= hi;
    }

    bool transcendentals::wide_interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val) {
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
        case transcendental_op_kind::TAN:
            // a pole strictly inside [lo, hi] makes tan unbounded there;
            // bail out and let the caller fall back to a tiny local box.
            if (contains_multiple_of(std::nextafter(lo, hi), std::nextafter(hi, lo), pi / 2, pi))
                return false;
            break;
        case transcendental_op_kind::COSH:
            // cosh is convex with its unique minimum (1) at 0.
            if (lo <= 0.0 && 0.0 <= hi) mn = 1.0;
            break;
        default:
            break; // monotonic on their whole domain: endpoints give the range.
        }
        double slack = std::max(error_bound(op, lo, f_lo), error_bound(op, hi, f_hi));
        lo_val = mn - slack;
        hi_val = mx + slack;
        return true;
    }

    bool transcendentals::check_app(app const& a) {
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        double x = xr.get_double();
        double y = yr.get_double();
        double fx = eval(a.op, x);
        if (!std::isfinite(fx))
            // out of the natural domain of op (e.g. asin/acos/atanh outside
            // [-1,1], or acosh for x < 1); this is not this check's
            // responsibility, some other part of the solver (e.g. the
            // OP_U_ASIN/OP_U_ACOS out-of-domain operators, or domain
            // constraints) is expected to handle it.
            return false;
        double tolerance = c.params().arith_nl_transcendental_tolerance();
        double err = error_bound(a.op, x, fx) + tolerance;
        if (std::fabs(y - fx) <= err)
            return false; // consistent within tolerance

        TRACE(nla_solver, tout << op_name(a.op) << "(" << xr << ") = " << yr
                               << " but floating point evaluation gives " << fx
                               << " +/- " << err << "\n";);

        // First, try arg's *actual* known bounds in the LP (if both sides
        // are finite) as the box: unlike the tiny box below, this does not
        // depend on the specific value x happened to take, so the
        // resulting lemma - if the wide box also exhibits an inconsistency
        // - is a reusable, genuinely more general fact about op restricted
        // to that already-asserted range, closer to the paper's Algorithm 2.
        if (c.lra.column_has_lower_bound(a.arg) && c.lra.column_has_upper_bound(a.arg)) {
            rational const& blo = c.lra.get_lower_bound(a.arg).x;
            rational const& bhi = c.lra.get_upper_bound(a.arg).x;
            double wflo, wfhi;
            if (wide_interval_eval(a.op, blo.get_double(), bhi.get_double(), wflo, wfhi)) {
                wflo = std::min(wflo, fx); // the box surely contains x too.
                wfhi = std::max(wfhi, fx);
                if (y < wflo) {
                    rational rflo = to_rational(wflo);
                    lemma_builder lemma(c, "transcendental range refinement: arg outside known bounds or val below enclosure");
                    lemma |= ineq(a.arg, lp::lconstraint_kind::LT, blo);
                    lemma |= ineq(a.arg, lp::lconstraint_kind::GT, bhi);
                    lemma |= ineq(a.val, lp::lconstraint_kind::GE, rflo);
                    ++c.lp_settings().stats().m_nla_transcendental_splits;
                    return true;
                }
                if (y > wfhi) {
                    rational rfhi = to_rational(wfhi);
                    lemma_builder lemma(c, "transcendental range refinement: arg outside known bounds or val above enclosure");
                    lemma |= ineq(a.arg, lp::lconstraint_kind::LT, blo);
                    lemma |= ineq(a.arg, lp::lconstraint_kind::GT, bhi);
                    lemma |= ineq(a.val, lp::lconstraint_kind::LE, rfhi);
                    ++c.lp_settings().stats().m_nla_transcendental_splits;
                    return true;
                }
                // the known bounds are too wide to expose an inconsistency
                // (op's range over them already covers y); fall through to
                // the tiny local box, which is guaranteed to work.
            }
        }

        // Bracket arg's current value in a small box and compute a
        // (floating point) enclosure of op over that box; see the module
        // comment for how this mirrors the paper's Algorithm 2. The box
        // bounds are derived from xr in exact rational arithmetic (rather
        // than by converting x +/- w back to rational) so that rlo < xr <
        // rhi holds unconditionally, regardless of double rounding.
        double w = std::max(tolerance, 1e-6) * std::max(1.0, std::fabs(x));
        rational rw = to_rational(w);
        rational rlo = xr - rw, rhi = xr + rw;
        double flo, fhi;
        interval_eval(a.op, rlo.get_double(), rhi.get_double(), flo, fhi);
        // widen further to be safe: the box also contains x itself.
        flo = std::min(flo, fx);
        fhi = std::max(fhi, fx);

        bool have_lemma = false;
        if (y < flo) {
            rational rflo = to_rational(flo);
            lemma_builder lemma(c, "transcendental box refinement: arg outside box or val below enclosure");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, rlo);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, rhi);
            lemma |= ineq(a.val, lp::lconstraint_kind::GE, rflo);
            have_lemma = true;
        }
        else if (y > fhi) {
            rational rfhi = to_rational(fhi);
            lemma_builder lemma(c, "transcendental box refinement: arg outside box or val above enclosure");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, rlo);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, rhi);
            lemma |= ineq(a.val, lp::lconstraint_kind::LE, rfhi);
            have_lemma = true;
        }
        if (!have_lemma)
            // the box enclosure happens to already cover val (can occur
            // when the box straddles a non-monotonic region); fall back to
            // a plain case split on the input variable, which is always
            // sound regardless of the quality of the floating point
            // estimate.
            c.m_literals.push_back(ineq(a.arg, lp::lconstraint_kind::LE, xr));

        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    void transcendentals::check() {
        if (m_apps.empty() || !m_core.params().arith_nl_transcendental())
            return;
        for (auto const& a : m_apps)
            if (check_app(a))
                return; // one case split per round is enough
    }
}
