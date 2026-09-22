/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    transcendental_eval.cpp

Abstract:

    See transcendental_eval.h.

Author:

    Nikolaj Bjorner

--*/
#include "nlsat/transcendental_eval.h"
#include <cmath>
#include <limits>
#include <algorithm>

namespace nlsat {
namespace transcendental_eval {

    char const* op_name(op_kind op) {
        switch (op) {
        case op_kind::SIN:   return "sin";
        case op_kind::COS:   return "cos";
        case op_kind::TAN:   return "tan";
        case op_kind::ASIN:  return "asin";
        case op_kind::ACOS:  return "acos";
        case op_kind::ATAN:  return "atan";
        case op_kind::SINH:  return "sinh";
        case op_kind::COSH:  return "cosh";
        case op_kind::TANH:  return "tanh";
        case op_kind::ASINH: return "asinh";
        case op_kind::ACOSH: return "acosh";
        case op_kind::ATANH: return "atanh";
        case op_kind::EXP:   return "exp";
        case op_kind::LOG:   return "log";
        }
        return "?";
    }

    double eval(op_kind op, double x) {
        switch (op) {
        case op_kind::SIN:   return std::sin(x);
        case op_kind::COS:   return std::cos(x);
        case op_kind::TAN:   return std::tan(x);
        // std::asin/std::acos return NaN outside [-1,1]; OP_U_ASIN/OP_U_ACOS
        // are the separate operators z3 uses for that out-of-domain case, so
        // NaN here is expected and handled by callers (isfinite checks).
        case op_kind::ASIN:  return std::asin(x);
        case op_kind::ACOS:  return std::acos(x);
        case op_kind::ATAN:  return std::atan(x);
        case op_kind::SINH:  return std::sinh(x);
        case op_kind::COSH:  return std::cosh(x);
        case op_kind::TANH:  return std::tanh(x);
        case op_kind::ASINH: return std::asinh(x);
        case op_kind::ACOSH: return std::acosh(x); // NaN for x < 1
        case op_kind::ATANH: return std::atanh(x); // NaN/+-inf for |x| >= 1
        case op_kind::EXP:   return std::exp(x);
        case op_kind::LOG:   return std::log(x); // NaN for x<0, -inf for x==0
        }
        return std::numeric_limits<double>::quiet_NaN();
    }

    double error_bound(op_kind op, double x, double fx) {
        double const eps = std::numeric_limits<double>::epsilon();
        double const safety = 64.0;       // generous margin, this is not a tight certificate
        double const boundary_safety = 4096.0; // extra margin near domain boundaries/poles
        switch (op) {
        case op_kind::SIN:
        case op_kind::COS:
        case op_kind::ATAN:
        case op_kind::TANH:
        case op_kind::ASINH:
            return safety * eps * std::max(1.0, std::fabs(x));
        case op_kind::SINH:
        case op_kind::COSH:
        case op_kind::EXP:
            return safety * eps * std::max(1.0, std::fabs(fx));
        case op_kind::TAN:
        case op_kind::ASIN:
        case op_kind::ACOS:
        case op_kind::ATANH:
        case op_kind::ACOSH:
        case op_kind::LOG: // derivative 1/x blows up as x -> 0+
            return boundary_safety * eps * std::max(1.0, std::max(std::fabs(x), std::fabs(fx)));
        }
        return 1e-6;
    }

    rational to_rational(double d) {
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

    void interval_eval(op_kind op, double lo, double hi, double& lo_val, double& hi_val) {
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

    bool wide_interval_eval(op_kind op, double lo, double hi, double& lo_val, double& hi_val) {
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
        case op_kind::SIN:
            if (contains_multiple_of(lo, hi, pi / 2, two_pi)) mx = 1.0;
            if (contains_multiple_of(lo, hi, -pi / 2, two_pi)) mn = -1.0;
            break;
        case op_kind::COS:
            if (contains_multiple_of(lo, hi, 0.0, two_pi)) mx = 1.0;
            if (contains_multiple_of(lo, hi, pi, two_pi)) mn = -1.0;
            break;
        case op_kind::TAN:
            // a pole strictly inside [lo, hi] makes tan unbounded there;
            // bail out and let the caller fall back to a tiny local box.
            if (contains_multiple_of(std::nextafter(lo, hi), std::nextafter(hi, lo), pi / 2, pi))
                return false;
            break;
        case op_kind::COSH:
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

    bool exp_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
        constexpr unsigned k_terms = 40;
        if (xr <= rational(0) && xr > rational(-static_cast<int>(k_terms))) {
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
            return true;
        }
        if (xr > rational(0) && xr < rational(k_terms + 1)) {
            rational term(1); // x^0/0!
            rational sum(0);
            for (unsigned k = 0; k < k_terms; ++k) {
                sum += term;
                term = term * xr / rational(k + 1);
            }
            rational q = xr / rational(k_terms + 1);
            lo = sum;
            hi = sum + term / (rational(1) - q);
            return true;
        }
        return false;
    }

    bool log_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
        if (xr < rational(1) || xr > rational(2))
            return false;
        rational u = xr - rational(1);
        constexpr unsigned k_terms = 60;
        rational term = u; // u^1/1
        rational sum(0);
        lo = sum; hi = sum;
        for (unsigned n = 1; n <= k_terms; ++n) {
            rational next = (n % 2 == 1) ? sum + term : sum - term;
            lo = std::min(sum, next);
            hi = std::max(sum, next);
            sum = next;
            term = term * u * rational(n) / rational(n + 1);
        }
        return true;
    }

    bool atan_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
        if (xr < rational(-1) || xr > rational(1))
            return false;
        constexpr unsigned k_terms = 40;
        rational term = xr;
        rational xr2 = xr * xr;
        rational sum(0);
        lo = sum; hi = sum;
        for (unsigned k = 0; k < k_terms; ++k) {
            rational next = sum + term / rational(2 * k + 1);
            lo = std::min(sum, next);
            hi = std::max(sum, next);
            sum = next;
            term = -term * xr2;
        }
        return true;
    }

}
}
