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

    // Default number of Taylor terms to seed every newly registered SIN/COS
    // application with, before any delta-check failure has been observed:
    // a small, cheap sandwich (degree 5 for sin, degree 4 for cos) that
    // still gives nlsat *some* algebraic connection between arg and val
    // from the very first call, rather than none at all. check_app bumps
    // this up further (never down) once an actual faulty model is seen at
    // a specific arg, so most applications never need more than this.
    static constexpr unsigned k_default_taylor_terms = 3;

    void transcendentals::add_transcendental(transcendental_op_kind op, lpvar arg, lpvar val) {
        if (arg == null_lpvar || val == null_lpvar)
            return;
        app a{ op, arg, val };
        taylor_bounds tb;
        if (get_taylor(op, k_default_taylor_terms, tb))
            a.taylor_terms = k_default_taylor_terms;
        m_apps.push_back(a);
        m_core.trail().push(push_back_vector(m_apps));
        add_range_axioms(op, val);

        // Look for a previously-registered application with the same
        // (structural) argument and a complementary op, to record an exact
        // cross-application identity pair (see the module comment). Only
        // considers apps registered *before* this one to avoid recording
        // the same pair twice if this function is ever called again for
        // the same (op, arg).
        for (unsigned i = 0; i + 1 < m_apps.size(); ++i) {
            app const& other = m_apps[i];
            if (other.arg != arg)
                continue;
            if (op == transcendental_op_kind::SIN && other.op == transcendental_op_kind::COS) {
                m_sin_cos_pairs.push_back({ val, other.val });
                m_core.trail().push(push_back_vector(m_sin_cos_pairs));
            }
            else if (op == transcendental_op_kind::COS && other.op == transcendental_op_kind::SIN) {
                m_sin_cos_pairs.push_back({ other.val, val });
                m_core.trail().push(push_back_vector(m_sin_cos_pairs));
            }
            else if (op == transcendental_op_kind::SINH && other.op == transcendental_op_kind::COSH) {
                m_cosh_sinh_pairs.push_back({ other.val, val });
                m_core.trail().push(push_back_vector(m_cosh_sinh_pairs));
            }
            else if (op == transcendental_op_kind::COSH && other.op == transcendental_op_kind::SINH) {
                m_cosh_sinh_pairs.push_back({ val, other.val });
                m_core.trail().push(push_back_vector(m_cosh_sinh_pairs));
            }
            else if (op == transcendental_op_kind::TANH && other.op == transcendental_op_kind::COSH) {
                m_cosh_tanh_pairs.push_back({ other.val, val });
                m_core.trail().push(push_back_vector(m_cosh_tanh_pairs));
            }
            else if (op == transcendental_op_kind::COSH && other.op == transcendental_op_kind::TANH) {
                m_cosh_tanh_pairs.push_back({ val, other.val });
                m_core.trail().push(push_back_vector(m_cosh_tanh_pairs));
            }
        }
    }

    void transcendentals::add_pi(lpvar val) {
        if (val == null_lpvar || m_pi_var != null_lpvar)
            return;
        m_core.trail().push(value_trail(m_pi_var, val));
        m_pi_var = val;
        // Same tight, exact-rational two-sided bound theory_lra used to
        // assert directly on pi's term (see arith_solver/theory_lra's
        // internalize_term): rationals strictly between the true
        // (irrational) value of pi, tight enough (~1e-14) for typical
        // benchmarks that compare against pi or small rational multiples
        // of it. Asserted here (rather than only in theory_lra) so pi's
        // range axiom lives alongside the other permanent range axioms in
        // this module.
        rational lo("3.14159265358979");
        rational hi("3.14159265358980");
        m_core.lra.add_var_bound(val, lp::lconstraint_kind::GE, lo);
        m_core.lra.add_var_bound(val, lp::lconstraint_kind::LE, hi);
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
        case transcendental_op_kind::EXP:
            // Sign constraint (TOCL/MathSAT paper): exp(x) > 0 for every x.
            // The tighter, still-unconditional exp(x) >= 1+x fact is
            // asserted reactively as a lemma instead (see
            // check_exp_lower_bound), since it is a two-column inequality
            // and this permanent-axiom path is single-column only.
            lra.add_var_bound(val, lp::lconstraint_kind::GT, rational(0));
            break;
        default:
            break; // TAN, SINH, ASINH, ATANH: no simple unconditional bound.
        }
    }

    void transcendentals::add_atan2(lpvar y, lpvar x, lpvar val) {
        if (y == null_lpvar || x == null_lpvar || val == null_lpvar)
            return;
        m_atan2_apps.push_back({ y, x, val });
        m_core.trail().push(push_back_vector(m_atan2_apps));
        // Permanent range axiom: atan2's range is (-pi, pi]; k_pi_ub is an
        // outward-rounded rational upper bound for pi (see above), so
        // asserting val <= k_pi_ub and val >= -k_pi_ub is sound (slightly
        // looser at -pi than the true half-open range, which does not
        // exclude any value atan2 can actually attain).
        m_core.lra.add_var_bound(val, lp::lconstraint_kind::LE, to_rational(k_pi_ub));
        m_core.lra.add_var_bound(val, lp::lconstraint_kind::GE, to_rational(-k_pi_ub));
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
        case transcendental_op_kind::EXP:   return "exp";
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
        case transcendental_op_kind::EXP:   return std::exp(x);
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
        case transcendental_op_kind::EXP:
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

    // Maclaurin (Taylor-at-0) polynomial sandwiches, sound for every real x
    // (not just a local box) via Lagrange's remainder theorem: sin and cos
    // are entire with all derivatives bounded by 1 in absolute value, so
    // truncating their Maclaurin series after num_terms terms leaves a
    // remainder bounded by |x|^p/p! for p the next power (p = last included
    // power + 1 for sin, + 2 for cos). Both cases land on an even p (sin's
    // last included power is odd, so +1 is even; cos's is already even, so
    // +2 keeps it even): this makes remainder_coeff*x^remainder_power
    // manifestly non-negative without needing |x|, so the sandwich can be
    // asserted without a case split on the sign of x. num_terms == 5
    // reproduces the fixed degree-9 (sin) / degree-8 (cos) sandwich this
    // module started out with.
    bool transcendentals::get_taylor(transcendental_op_kind op, unsigned num_terms, taylor_bounds& out) {
        if (num_terms == 0)
            return false;
        bool is_sin;
        switch (op) {
        case transcendental_op_kind::SIN: is_sin = true; break;
        case transcendental_op_kind::COS: is_sin = false; break;
        default: return false;
        }
        out.poly.clear();
        auto factorial = [](unsigned n) {
            rational r(1);
            for (unsigned k = 2; k <= n; ++k)
                r *= rational(k);
            return r;
        };
        unsigned last_power = 0;
        for (unsigned i = 0; i < num_terms; ++i) {
            unsigned power = is_sin ? 2 * i + 1 : 2 * i;
            rational coeff = rational(1) / factorial(power);
            if (i % 2 != 0)
                coeff = -coeff;
            out.poly.push_back({ coeff, power });
            last_power = power;
        }
        out.remainder_power = last_power + (is_sin ? 1 : 2);
        out.remainder_coeff = rational(1) / factorial(out.remainder_power);
        return true;
    }

    // Picks the smallest Taylor degree (in the floating point sense; the
    // eventual axiom is exact rational arithmetic, this is only a heuristic
    // for choosing how many terms to bother with) that would exclude the
    // observed faulty model (x, y): the sandwich guarantees op(x) is within
    // rk of T_k(x), so if y is more than 2*rk away from T_k(x) it cannot lie
    // in [T_k(x)-rk, T_k(x)+rk] and the axiom directly contradicts y.
    unsigned transcendentals::degree_to_exclude(transcendental_op_kind op, double x, double y, unsigned max_terms) {
        for (unsigned k = 1; k <= max_terms; ++k) {
            taylor_bounds tb;
            if (!get_taylor(op, k, tb))
                return 0;
            double tk = 0.0;
            for (auto const& t : tb.poly)
                tk += t.coeff.get_double() * std::pow(x, static_cast<int>(t.power));
            double rk = tb.remainder_coeff.get_double() * std::pow(std::fabs(x), static_cast<int>(tb.remainder_power));
            if (2.0 * rk < std::fabs(y - tk))
                return k;
        }
        return 0; // |x| too large (or y too close to op(x)) for this to help
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

    bool transcendentals::has_linear_majorant(transcendental_op_kind op) {
        switch (op) {
        case transcendental_op_kind::SIN:
        case transcendental_op_kind::TANH:
        case transcendental_op_kind::ATAN:
            return true;
        default:
            return false;
        }
    }

    bool transcendentals::check_linear_majorant(app& a) {
        if (!has_linear_majorant(a.op))
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        // val - arg, used as the two-variable term for the "val <= arg" /
        // "val >= arg" literal below.
        lp::lar_term diff(rational(1), a.val, rational(-1), a.arg);
        if (xr.is_nonneg() && yr > xr) {
            lemma_builder lemma(c, "transcendental linear majorant: arg negative or val <= arg");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, rational(0));
            lemma |= ineq(diff, lp::lconstraint_kind::LE, rational(0));
            ++c.lp_settings().stats().m_nla_transcendental_splits;
            return true;
        }
        if (xr.is_nonpos() && yr < xr) {
            lemma_builder lemma(c, "transcendental linear majorant: arg positive or val >= arg");
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, rational(0));
            lemma |= ineq(diff, lp::lconstraint_kind::GE, rational(0));
            ++c.lp_settings().stats().m_nla_transcendental_splits;
            return true;
        }
        return false;
    }

    bool transcendentals::check_sign_on_pi_range(app& a) {
        if (m_pi_var == null_lpvar)
            return false;
        if (a.op != transcendental_op_kind::SIN && a.op != transcendental_op_kind::COS)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        rational const& pr = c.val(m_pi_var);

        if (a.op == transcendental_op_kind::SIN) {
            // sin(t) > 0 for 0 < t < pi.
            if (xr.is_pos() && xr < pr && !yr.is_pos()) {
                lp::lar_term diff(rational(1), a.arg, rational(-1), m_pi_var); // arg - pi
                lemma_builder lemma(c, "transcendental sign: sin(arg) > 0 on (0, pi)");
                lemma |= ineq(a.arg, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(diff, lp::lconstraint_kind::GE, rational(0));
                lemma |= ineq(a.val, lp::lconstraint_kind::GT, rational(0));
                ++c.lp_settings().stats().m_nla_transcendental_splits;
                return true;
            }
            // sin(t) < 0 for -pi < t < 0.
            if (xr.is_neg() && xr > -pr && !yr.is_neg()) {
                lp::lar_term sum(rational(1), a.arg, rational(1), m_pi_var); // arg + pi
                lemma_builder lemma(c, "transcendental sign: sin(arg) < 0 on (-pi, 0)");
                lemma |= ineq(a.arg, lp::lconstraint_kind::GE, rational(0));
                lemma |= ineq(sum, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(a.val, lp::lconstraint_kind::LT, rational(0));
                ++c.lp_settings().stats().m_nla_transcendental_splits;
                return true;
            }
            return false;
        }

        // COS: use the doubled argument 2*arg vs +/-pi so no separate
        // pi/2 variable is needed.
        // cos(t) > 0 for -pi/2 < t < pi/2, i.e. -pi < 2t < pi.
        if (2 * xr > -pr && 2 * xr < pr && !yr.is_pos()) {
            lp::lar_term lo_term(rational(2), a.arg, rational(1), m_pi_var);  // 2*arg + pi
            lp::lar_term hi_term(rational(2), a.arg, rational(-1), m_pi_var); // 2*arg - pi
            lemma_builder lemma(c, "transcendental sign: cos(arg) > 0 on (-pi/2, pi/2)");
            lemma |= ineq(lo_term, lp::lconstraint_kind::LE, rational(0));
            lemma |= ineq(hi_term, lp::lconstraint_kind::GE, rational(0));
            lemma |= ineq(a.val, lp::lconstraint_kind::GT, rational(0));
            ++c.lp_settings().stats().m_nla_transcendental_splits;
            return true;
        }
        // cos(t) < 0 for pi/2 < t < 3pi/2, i.e. pi < 2t < 3pi.
        if (2 * xr > pr && 2 * xr < 3 * pr && !yr.is_neg()) {
            lp::lar_term lo_term(rational(2), a.arg, rational(-1), m_pi_var); // 2*arg - pi
            lp::lar_term hi_term(rational(2), a.arg, rational(-3), m_pi_var); // 2*arg - 3*pi
            lemma_builder lemma(c, "transcendental sign: cos(arg) < 0 on (pi/2, 3pi/2)");
            lemma |= ineq(lo_term, lp::lconstraint_kind::LE, rational(0));
            lemma |= ineq(hi_term, lp::lconstraint_kind::GE, rational(0));
            lemma |= ineq(a.val, lp::lconstraint_kind::LT, rational(0));
            ++c.lp_settings().stats().m_nla_transcendental_splits;
            return true;
        }
        return false;
    }

    bool transcendentals::check_exp_lower_bound(app& a) {
        if (a.op != transcendental_op_kind::EXP)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        if (yr >= rational(1) + xr)
            return false; // exp(x) >= 1+x already holds, nothing to do.
        // val - arg >= 1, i.e. val >= 1 + arg; sound for every real arg
        // (TOCL/MathSAT paper's degree-1 Maclaurin lower bound, which for
        // exp coincides with the tangent line at 0 - unlike a tangent
        // line at an arbitrary point, this one needs no case split and no
        // floating point point-evaluation to be sound), so this is
        // asserted as a single-literal lemma.
        lp::lar_term diff(rational(1), a.val, rational(-1), a.arg); // val - arg
        lemma_builder lemma(c, "transcendental exp lower bound: exp(arg) >= 1+arg");
        lemma |= ineq(diff, lp::lconstraint_kind::GE, rational(1));
        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    bool transcendentals::check_exp_monotonicity(app& a) {
        if (a.op != transcendental_op_kind::EXP)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        for (auto const& other : m_apps) {
            if (other.op != transcendental_op_kind::EXP || other.arg == a.arg)
                continue;
            rational const& xr2 = c.val(other.arg);
            rational const& yr2 = c.val(other.val);
            // Monotonicity constraint (TOCL/MathSAT paper): x1 < x2 =>
            // exp(x1) < exp(x2). Checked both ways (a vs other) so a
            // single pairwise scan catches either orientation. Expressed
            // via lar_terms relating the two applications' variables
            // symbolically (not the current concrete values), so the
            // resulting lemma is a genuine, reusable fact about the
            // relationship between the two applications, rather than one
            // tied to this particular round's witness values (which would
            // never converge, since a fresh pair of concrete values would
            // trip the same check again next round).
            lp::lar_term arg_diff(rational(1), a.arg, rational(-1), other.arg); // a.arg - other.arg
            lp::lar_term val_diff(rational(1), a.val, rational(-1), other.val); // a.val - other.val
            if (xr < xr2 && yr >= yr2) {
                lemma_builder lemma(c, "transcendental exp monotonicity");
                lemma |= ineq(arg_diff, lp::lconstraint_kind::GE, rational(0));
                lemma |= ineq(val_diff, lp::lconstraint_kind::LT, rational(0));
                ++c.lp_settings().stats().m_nla_transcendental_splits;
                return true;
            }
            if (xr > xr2 && yr <= yr2) {
                lemma_builder lemma(c, "transcendental exp monotonicity");
                lemma |= ineq(arg_diff, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(val_diff, lp::lconstraint_kind::GT, rational(0));
                ++c.lp_settings().stats().m_nla_transcendental_splits;
                return true;
            }
        }
        return false;
    }

    bool transcendentals::check_atan_taylor_range(app& a) {
        if (a.op != transcendental_op_kind::ATAN)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        if (xr < rational(-1) || xr > rational(1))
            return false; // outside the Maclaurin series' radius of convergence.
        rational const& yr = c.val(a.val);
        // atan(x) = x - x^3/3 + x^5/5 - ... ; for |x| <= 1 the terms are
        // non-increasing in magnitude, so by the alternating series
        // estimation theorem every partial sum S_k brackets the true
        // value together with S_{k+1}: min(S_k, S_{k+1}) <= atan(x) <=
        // max(S_k, S_{k+1}). Computed here in exact rational arithmetic
        // (unlike the generic float-based box-refinement fallback), so
        // the resulting bracket is an exact, not just floating point
        // approximate, enclosure - but, since S_k(xr) is evaluated at
        // this specific xr, it is only sound exactly at arg = xr, not
        // over the whole [-1,1] domain (unlike check_linear_majorant's
        // fact, which is uniform over an entire half-line); the lemma
        // below therefore gates on arg == xr exactly (a point exclusion,
        // in the same spirit as check_app's plain case-split fallback),
        // not on the domain condition.
        constexpr unsigned k_terms = 40;
        rational term = xr;
        rational xr2 = xr * xr;
        rational sum(0);
        rational lo = sum, hi = sum;
        for (unsigned k = 0; k < k_terms; ++k) {
            rational next = sum + term / rational(2 * k + 1);
            lo = std::min(sum, next);
            hi = std::max(sum, next);
            sum = next;
            term = -term * xr2;
        }
        if (yr >= lo && yr <= hi)
            return false; // already consistent with the bracket.
        if (yr < lo) {
            lemma_builder lemma(c, "transcendental atan Maclaurin lower bound");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, xr);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, xr);
            lemma |= ineq(a.val, lp::lconstraint_kind::GE, lo);
        }
        else {
            lemma_builder lemma(c, "transcendental atan Maclaurin upper bound");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, xr);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, xr);
            lemma |= ineq(a.val, lp::lconstraint_kind::LE, hi);
        }
        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    bool transcendentals::check_exp_taylor_range(app& a) {
        if (a.op != transcendental_op_kind::EXP)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        // Two exact rational brackets, depending on the sign of x:
        //  - x <= 0: exp(x) = sum x^n/n! is a genuine alternating series
        //    (term_n = x^n/n!, sign (-1)^n since x <= 0); once n+1 >= |x|
        //    the term magnitude |x|^n/n! is non-increasing, so the
        //    alternating series estimation theorem brackets the value
        //    between consecutive partial sums from that point on (see
        //    below for how the possibly non-monotone initial terms are
        //    handled).
        //  - x > 0 (and small enough that k_terms+1 > x): all terms are
        //    positive, so partial sums increase monotonically towards
        //    exp(x) (a sound lower bound), and the omitted tail is
        //    bracketed by a geometric series (see below) for the upper
        //    bound.
        // This closes a gap that check_exp_lower_bound (only the k=1
        // tangent-line bound, exp(x) >= 1+x) leaves open: near x = 0 the
        // tangent bound alone permits exp(x) to be set arbitrarily far
        // above its true value without tripping any lemma, which can flip
        // the sign of an otherwise-infeasible inequality whose margin
        // vanishes as x -> 0 (and analogously elsewhere on x > 0, where
        // the tangent bound alone gives no upper bound at all).
        constexpr unsigned k_terms = 40;
        rational const& yr = c.val(a.val);
        rational lo, hi;
        if (xr <= rational(0) && xr > rational(-static_cast<int>(k_terms))) {
            // x <= 0: term_n = x^n/n! alternates in sign; its magnitude
            // |x|^n/n! is non-increasing once n+1 >= |x| (ratio
            // |x|/(n+1) <= 1). Compute the exact prefix sum S_{n0} for the
            // (possibly non-monotone) initial terms n = 0 .. n0-1 directly
            // - no bracket needed there, they're exact rationals - then
            // apply the alternating-series bracket from n0 onward, where
            // it is valid. n0 = 0 whenever |x| <= 1 (the previously fixed
            // special case is the n0 == 0 instance of this).
            rational ax = -xr;
            unsigned n0 = 0;
            while (rational(n0 + 1) < ax)
                ++n0;
            rational term(1); // x^0 / 0!
            rational sum(0);
            for (unsigned k = 0; k < n0; ++k) {
                sum += term;
                term = term * xr / rational(k + 1);
            }
            lo = sum; hi = sum;
            for (unsigned k = n0; k < k_terms; ++k) {
                rational next = sum + term;
                lo = std::min(sum, next);
                hi = std::max(sum, next);
                sum = next;
                term = term * xr / rational(k + 1);
            }
        }
        else if (xr > rational(0) && xr < rational(k_terms + 1)) {
            // x > 0: all terms term_n = x^n/n! are positive, so the
            // partial sums S_n increase monotonically towards exp(x),
            // giving a sound lower bound directly. For the upper bound,
            // bracket the omitted tail sum_{k>=n} x^k/k! by a geometric
            // series: term_k/term_n <= (x/(n+1))^(k-n) once the ratio
            // q = x/(n+1) < 1 (guaranteed by the domain guard above), so
            // the tail is <= term_n / (1 - q), an exact rational bound.
            rational term(1); // x^0/0!
            rational sum(0);
            for (unsigned k = 0; k < k_terms; ++k) {
                sum += term;
                term = term * xr / rational(k + 1);
            }
            // here `term` is term_{k_terms} = x^{k_terms}/k_terms!, and
            // `sum` = S_{k_terms} (k_terms terms included).
            rational q = xr / rational(k_terms + 1);
            lo = sum;
            hi = sum + term / (rational(1) - q);
        }
        else
            return false;
        if (yr >= lo && yr <= hi)
            return false; // already consistent with the bracket.
        if (yr < lo) {
            lemma_builder lemma(c, "transcendental exp Maclaurin lower bound");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, xr);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, xr);
            lemma |= ineq(a.val, lp::lconstraint_kind::GE, lo);
        }
        else {
            lemma_builder lemma(c, "transcendental exp Maclaurin upper bound");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, xr);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, xr);
            lemma |= ineq(a.val, lp::lconstraint_kind::LE, hi);
        }
        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    bool transcendentals::check_sin_cos_taylor_range(app& a) {
        if (a.op != transcendental_op_kind::SIN && a.op != transcendental_op_kind::COS)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        // sin/cos are entire, so get_taylor's sandwich is valid for any
        // |arg|; the cutoff below only keeps the exact rational arithmetic
        // (and the remainder bound itself) small/tight enough to be worth
        // computing - for large |arg| this many terms would neither be
        // cheap nor tight, and check_sign_on_pi_range/the general box
        // refinement in check_app already cover that case.
        if (xr < rational(-8) || xr > rational(8))
            return false;
        rational const& yr = c.val(a.val);
        constexpr unsigned k_terms = 20;
        taylor_bounds tb;
        if (!get_taylor(a.op, k_terms, tb))
            return false;
        rational sum(0);
        for (auto const& t : tb.poly)
            sum += t.coeff * xr.expt(static_cast<int>(t.power));
        // remainder_power is always even (see get_taylor), so this is
        // manifestly non-negative without needing |xr|.
        rational bound = tb.remainder_coeff * xr.expt(static_cast<int>(tb.remainder_power));
        rational lo = sum - bound, hi = sum + bound;
        if (yr >= lo && yr <= hi)
            return false; // already consistent with the bracket.
        if (yr < lo) {
            lemma_builder lemma(c, "transcendental sin/cos Maclaurin lower bound");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, xr);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, xr);
            lemma |= ineq(a.val, lp::lconstraint_kind::GE, lo);
        }
        else {
            lemma_builder lemma(c, "transcendental sin/cos Maclaurin upper bound");
            lemma |= ineq(a.arg, lp::lconstraint_kind::LT, xr);
            lemma |= ineq(a.arg, lp::lconstraint_kind::GT, xr);
            lemma |= ineq(a.val, lp::lconstraint_kind::LE, hi);
        }
        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    bool transcendentals::check_atan2(atan2_app& a) {
        core& c = m_core;
        rational const& yr = c.val(a.y);
        rational const& xr = c.val(a.x);
        rational const& vr = c.val(a.val);
        // Sign fact: sign(atan2(y,x)) == sign(y) whenever y != 0, for
        // every x (atan2's quadrant selection never flips the sign of the
        // result relative to y - it only ever affects how close |val| is
        // to pi vs 0).
        if (yr.is_pos() && !vr.is_pos()) {
            lemma_builder lemma(c, "transcendental atan2 sign: y > 0 => atan2(y,x) > 0");
            lemma |= ineq(a.y, lp::lconstraint_kind::LE, rational(0));
            lemma |= ineq(a.val, lp::lconstraint_kind::GT, rational(0));
            ++c.lp_settings().stats().m_nla_transcendental_splits;
            return true;
        }
        if (yr.is_neg() && !vr.is_neg()) {
            lemma_builder lemma(c, "transcendental atan2 sign: y < 0 => atan2(y,x) < 0");
            lemma |= ineq(a.y, lp::lconstraint_kind::GE, rational(0));
            lemma |= ineq(a.val, lp::lconstraint_kind::LT, rational(0));
            ++c.lp_settings().stats().m_nla_transcendental_splits;
            return true;
        }
        double y = yr.get_double(), x = xr.get_double(), v = vr.get_double();
        double fv = std::atan2(y, x);
        if (!std::isfinite(fv))
            return false; // (0,0): undefined, not this check's responsibility.
        double tolerance = c.params().arith_nl_transcendental_tolerance();
        // atan2 has a branch cut, so its derivative is unbounded near
        // x < 0, y ~ 0 (val jumps by ~2*pi there); use a generous margin
        // rather than attempting a tight closed-form error bound.
        double err = 4096.0 * std::numeric_limits<double>::epsilon() * std::max(1.0, std::fabs(fv)) + tolerance;
        if (std::fabs(v - fv) <= err)
            return false;
        // Coarse case-split fallback on sign(x), rather than a full 2D
        // box-refinement enclosure (atan2's branch structure makes a tight
        // closed-form box substantially more involved - out of scope
        // here; see the module comment). This is always sound: it merely
        // forces the search to commit to one quadrant-determining fact at
        // a time, in the same spirit as check_app's plain case-split
        // fallback.
        c.m_literals.push_back(ineq(a.x, lp::lconstraint_kind::LE, xr));
        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    bool transcendentals::check_app(app& a) {
        core& c = m_core;
        if (check_linear_majorant(a))
            return true;
        if (check_sign_on_pi_range(a))
            return true;
        if (check_exp_lower_bound(a))
            return true;
        if (check_exp_taylor_range(a))
            return true;
        if (check_exp_monotonicity(a))
            return true;
        if (check_atan_taylor_range(a))
            return true;
        if (check_sin_cos_taylor_range(a))
            return true;
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

        // A genuine delta-check failure: this is the only point at which
        // it is worth paying for a Taylor sandwich axiom for this
        // application at all. Bump (never lower) the recorded degree to
        // just enough to exclude this specific faulty witness, so the next
        // nra_solver invocation (bounded_nlsat or the main nra check) gets
        // an axiom that actually rules the current (arg, val) assignment
        // out, rather than an eagerly-asserted, possibly much higher degree
        // polynomial that was never needed.
        ++m_num_failures;
        unsigned need = degree_to_exclude(a.op, x, y);
        if (need > a.taylor_terms)
            a.taylor_terms = need;

        TRACE(nla_solver, tout << op_name(a.op) << "(" << xr << ") = " << yr
                               << " but floating point evaluation gives " << fx
                               << " +/- " << err << " (taylor_terms now " << a.taylor_terms << ")\n";);

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
        if (empty() || !m_core.params().arith_nl_transcendental())
            return;
        for (auto& a : m_apps)
            if (check_app(a))
                return; // one case split per round is enough
        for (auto& a : m_atan2_apps)
            if (check_atan2(a))
                return;
    }

    bool transcendentals::check_nra_model() {
        core& c = m_core;
        if (!c.use_nra_model())
            return false;
        double tolerance = c.params().arith_nl_transcendental_tolerance();
        for (auto const& a : m_apps) {
            // No axiom asserted for this application yet (it has never
            // failed a delta-check): val is an opaque free real to nlsat,
            // exactly as before Taylor axioms existed at all. Accepting
            // that is no less sound than the established, already-tested
            // behavior of trusting nra_solver's l_true together with just
            // the unconditional range axioms; only tighten the check for
            // applications that *do* have an accumulated axiom, where we
            // can and should certify it is actually tight enough here.
            if (a.taylor_terms == 0)
                continue;
            taylor_bounds tb;
            if (!get_taylor(a.op, a.taylor_terms, tb))
                continue; // no certified sandwich for this op: nothing to certify against
            rational xlo, xhi;
            c.nra_model_bound(a.arg, xlo, xhi);
            rational xabs = std::max(abs(xlo), abs(xhi));
            rational remainder = tb.remainder_coeff * xabs.expt(tb.remainder_power);
            // the sandwich guarantees op(arg) lies within [-remainder,
            // remainder] of T(arg); val, per the nlsat clauses added for
            // this application, is itself within that same interval of
            // T(arg) (it's a hard constraint on the witness), so |val -
            // op(arg)| <= 2*remainder. Accept only if that is within the
            // documented approximation tolerance already used elsewhere for
            // transcendentals (arith.nl.transcendental_tolerance).
            if (2 * remainder > to_rational(tolerance))
                return false;
        }
        return true;
    }
}
