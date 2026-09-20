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
        case transcendental_op_kind::LOG:  return std::log(x); // NaN for x<0, -inf for x==0
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
        double const boundary_safety = 4096.0; // extra margin near the domain boundary (x -> 0+)
        switch (op) {
        case transcendental_op_kind::SIN:
        case transcendental_op_kind::COS:
        case transcendental_op_kind::ATAN:
            return safety * eps * std::max(1.0, std::fabs(x));
        case transcendental_op_kind::EXP:
            return safety * eps * std::max(1.0, std::fabs(fx));
        case transcendental_op_kind::LOG: // derivative 1/x blows up as x -> 0+
            return boundary_safety * eps * std::max(1.0, std::max(std::fabs(x), std::fabs(fx)));
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

    // ---- Exact rational Taylor/Maclaurin brackets, ported from
    // nla::transcendentals (math/lp/nla_transcendentals.cpp) ----

    // Exact rational Maclaurin bracket [lo, hi] for exp(x) at a single point
    // x: for x <= 0 the series sum x^n/n! is alternating once n+1 >= |x|
    // (skipping a possibly non-monotone initial run of terms before that),
    // so consecutive partial sums bracket the value from there on; for
    // x > 0 all terms are positive (a sound, monotonically increasing lower
    // bound), and the omitted tail from term k_terms+1 on is bounded by a
    // geometric series (ratio q = x/(k_terms+1) < 1) for the upper bound.
    bool transcendentals::exp_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
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

    // Exact rational Mercator (Taylor-at-1) bracket [lo, hi] for log(x),
    // valid only for 1 <= x <= 2: writing u = x-1 in [0,1], log(1+u) is a
    // genuine alternating series there, so consecutive partial sums bracket
    // the true value from the very first term.
    bool transcendentals::log_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
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

    // Exact rational Maclaurin bracket [lo, hi] for atan(x), valid only for
    // |x| <= 1 (the series' radius of convergence): atan(x) = x - x^3/3 +
    // x^5/5 - ... is a genuine alternating series there, so consecutive
    // partial sums bracket the true value.
    bool transcendentals::atan_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
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
            break; // EXP, ATAN, LOG: monotonic increasing everywhere on their domain, endpoints give the range.
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

    // Builds the literal c1*x1 + c2*x2 < bound (k == LT) or > bound
    // (k == GT), the two-variable analogue of bound_literal above, used by
    // the exact global tangent-line axioms and the cross-application
    // monotonicity lemmas below (e.g. c1=1,x1=val, c2=-1,x2=arg encodes
    // val-arg).
    static literal linear_literal(solver& s, var x1, rational const& c1, var x2, rational const& c2,
                                   atom::kind k, rational const& bound) {
        rational den = lcm(denominator(c1), lcm(denominator(c2), denominator(bound)));
        rational coeffs[2] = { c1 * den, c2 * den };
        var vars[2] = { x1, x2 };
        rational c = -(bound * den);
        polynomial_ref p(s.pm().mk_linear(2, coeffs, vars, c), s.pm());
        poly* pp = p.get();
        bool is_even = false;
        return s.mk_ineq_literal(k, 1, &pp, &is_even);
    }

    void transcendentals::add(transcendental_op_kind op, var arg, var val) {
        m_apps.push_back({ op, arg, val });
        m_retry.push_back(0);
        add_global_axioms(op, arg, val);
    }

    // Exact, unconditional (or, for LOG, disjunctively domain-guarded)
    // global tangent-line axioms, ported from
    // nla::transcendentals::check_exp_lower_bound / check_log_upper_bound.
    // Registered once, as permanent clauses, the moment the application is
    // known - unlike the Taylor sandwich (refine_app) these need no
    // witness-dependent widening, since a tangent line to a convex (exp) or
    // concave (log) function is a *global* bound.
    void transcendentals::add_global_axioms(transcendental_op_kind op, var arg, var val) {
        switch (op) {
        case transcendental_op_kind::EXP: {
            // exp(arg) >= 1+arg, i.e. NOT(val - arg < 1).
            literal lit = ~linear_literal(s, val, rational(1), arg, rational(-1), atom::LT, rational(1));
            s.mk_clause(1, &lit, nullptr);
            break;
        }
        case transcendental_op_kind::LOG: {
            // arg <= 0  \/  log(arg) <= arg-1, i.e. NOT(arg>0) \/ NOT(val-arg>-1).
            literal lits[2] = {
                ~bound_literal(s, arg, atom::GT, rational(0)),
                ~linear_literal(s, val, rational(1), arg, rational(-1), atom::GT, rational(-1))
            };
            s.mk_clause(2, lits, nullptr);
            break;
        }
        default:
            break; // SIN/COS/ATAN: no exact global linear bound; left to refine_app's Taylor sandwich.
        }
    }

    bool transcendentals::refine_app(unsigned idx) {
        app const& a = m_apps[idx];
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
        // *conflicting* bound required guarding against there. The
        // exclusion width grows exponentially with m_retry[idx] (doubling
        // every round this application is refined again) so that repeated
        // convergence toward a single fixed point - e.g. a tangent point of
        // one of add_global_axioms' bounds - is only ever a logarithmic
        // number of rounds from forcing nlsat far enough away to make
        // progress, rather than potentially unboundedly many rounds of
        // shrinking-by-a-constant-factor exclusions.
        rational amid = (l + u) / rational(2);
        if (amid.is_neg()) amid = -amid;
        rational scale = amid > rational(1) ? amid : rational(1);
        rational growth = rational::power_of_two(std::min(m_retry[idx], 30u));
        rational rdelta = rational(1, 1000000) * scale * growth;
        rational xlo = l - rdelta, xhi = u + rdelta;

        // Exact rational Taylor/Maclaurin bracket, when the argument (both
        // widened endpoints) falls inside the respective series' domain:
        // EXP, LOG and ATAN are all monotonically increasing there, so
        // bracket_at(xlo)'s lower half and bracket_at(xhi)'s upper half
        // together soundly enclose the op over the whole [xlo, xhi], with
        // no floating point round-off risk anywhere in the computation.
        rational rlo, rhi;
        bool have_exact = false;
        {
            rational lo1, hi1, lo2, hi2;
            switch (a.op) {
            case transcendental_op_kind::EXP:
                have_exact = exp_taylor_bracket_at(xlo, lo1, hi1) && exp_taylor_bracket_at(xhi, lo2, hi2);
                break;
            case transcendental_op_kind::LOG:
                have_exact = log_taylor_bracket_at(xlo, lo1, hi1) && log_taylor_bracket_at(xhi, lo2, hi2);
                break;
            case transcendental_op_kind::ATAN:
                have_exact = atan_taylor_bracket_at(xlo, lo1, hi1) && atan_taylor_bracket_at(xhi, lo2, hi2);
                break;
            default:
                break; // SIN/COS: not monotonic, use interval_eval's extremum-aware double enclosure instead.
            }
            if (have_exact) {
                rlo = lo1;
                rhi = hi2;
            }
        }

        anum const& yv = s.value(a.val);
        if (have_exact) {
            if (s.am().ge(yv, rlo.to_mpq()) && s.am().le(yv, rhi.to_mpq())) {
                m_retry[idx] = 0;
                return false; // already consistent with the exact enclosure.
            }
            literal_vector lemma;
            lemma.push_back(bound_literal(s, a.arg, atom::LT, xlo));
            lemma.push_back(bound_literal(s, a.arg, atom::GT, xhi));
            if (s.am().lt(yv, rlo.to_mpq()))
                lemma.push_back(~bound_literal(s, a.val, atom::LT, rlo)); // val >= rlo
            else
                lemma.push_back(~bound_literal(s, a.val, atom::GT, rhi)); // val <= rhi
            s.mk_clause(lemma.size(), lemma.data(), nullptr);
            ++m_retry[idx];
            return true;
        }

        // Fall back to the conservative floating point enclosure (SIN/COS,
        // or EXP/LOG/ATAN arguments outside their exact series' domain).
        double lo_d = xlo.get_double(), hi_d = xhi.get_double();
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
        rational rlo2 = to_rational(lo_val), rhi2 = to_rational(hi_val);
        if (s.am().ge(yv, rlo2.to_mpq()) && s.am().le(yv, rhi2.to_mpq())) {
            m_retry[idx] = 0;
            return false; // already consistent with the enclosure.
        }

        rational rxlo = to_rational(lo_d), rxhi = to_rational(hi_d);
        literal_vector lemma;
        lemma.push_back(bound_literal(s, a.arg, atom::LT, rxlo));
        lemma.push_back(bound_literal(s, a.arg, atom::GT, rxhi));
        if (s.am().lt(yv, rlo2.to_mpq()))
            lemma.push_back(~bound_literal(s, a.val, atom::LT, rlo2)); // val >= rlo2
        else
            lemma.push_back(~bound_literal(s, a.val, atom::GT, rhi2)); // val <= rhi2
        s.mk_clause(lemma.size(), lemma.data(), nullptr);
        ++m_retry[idx];
        return true;
    }

    // Cross-application monotonicity, ported from
    // nla::transcendentals::check_exp_monotonicity / check_log_monotonicity:
    // scans every pair of registered EXP or LOG applications and adds a
    // (symbolic, reusable - not tied to this round's witness values) lemma
    // the first time a pair's current witnesses violate x1 < x2 => op(x1) <
    // op(x2).
    bool transcendentals::refine_monotonicity_pair(app const& a, app const& b) {
        anum const& xa = s.value(a.arg);
        anum const& xb = s.value(b.arg);
        if (a.op == transcendental_op_kind::LOG && (!s.am().is_pos(xa) || !s.am().is_pos(xb)))
            return false; // log's monotonicity claim only applies to positive arguments.
        anum const& ya = s.value(a.val);
        anum const& yb = s.value(b.val);
        bool violated = false, a_lt_b = false;
        if (s.am().lt(xa, xb) && s.am().ge(ya, yb)) { violated = true; a_lt_b = true; }
        else if (s.am().lt(xb, xa) && s.am().ge(yb, ya)) { violated = true; a_lt_b = false; }
        if (!violated)
            return false;
        literal_vector lemma;
        if (a.op == transcendental_op_kind::LOG) {
            lemma.push_back(~bound_literal(s, a.arg, atom::GT, rational(0))); // a.arg <= 0
            lemma.push_back(~bound_literal(s, b.arg, atom::GT, rational(0))); // b.arg <= 0
        }
        if (a_lt_b) {
            // a.arg >= b.arg  \/  a.val < b.val
            lemma.push_back(~linear_literal(s, a.arg, rational(1), b.arg, rational(-1), atom::LT, rational(0)));
            lemma.push_back(linear_literal(s, a.val, rational(1), b.val, rational(-1), atom::LT, rational(0)));
        }
        else {
            // a.arg <= b.arg  \/  a.val > b.val
            lemma.push_back(~linear_literal(s, a.arg, rational(1), b.arg, rational(-1), atom::GT, rational(0)));
            lemma.push_back(linear_literal(s, a.val, rational(1), b.val, rational(-1), atom::GT, rational(0)));
        }
        s.mk_clause(lemma.size(), lemma.data(), nullptr);
        return true;
    }

    bool transcendentals::refine_monotonicity() {
        bool added = false;
        for (unsigned i = 0; i < m_apps.size(); ++i) {
            if (m_apps[i].op != transcendental_op_kind::EXP && m_apps[i].op != transcendental_op_kind::LOG)
                continue;
            for (unsigned j = i + 1; j < m_apps.size(); ++j) {
                if (m_apps[j].op != m_apps[i].op)
                    continue;
                if (refine_monotonicity_pair(m_apps[i], m_apps[j]))
                    added = true;
            }
        }
        return added;
    }

    bool transcendentals::refine() {
        bool added = false;
        for (unsigned i = 0; i < m_apps.size(); ++i)
            if (refine_app(i))
                added = true;
        if (refine_monotonicity())
            added = true;
        return added;
    }
}

