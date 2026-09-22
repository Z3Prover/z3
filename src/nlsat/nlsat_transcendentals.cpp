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
        return transcendental_eval::eval(op, x);
    }

    // See transcendental_eval::error_bound (util/transcendental_eval.cpp,
    // shared with nla::transcendentals::error_bound) for the implementation.
    double transcendentals::error_bound(transcendental_op_kind op, double x, double fx) {
        return transcendental_eval::error_bound(op, x, fx);
    }

    // Exact rational equal to the finite double d; see
    // transcendental_eval::to_rational for the shared implementation.
    rational transcendentals::to_rational(double d) {
        return transcendental_eval::to_rational(d);
    }

    // ---- Exact rational Taylor/Maclaurin brackets, shared with
    // nla::transcendentals (math/lp/nla_transcendentals.cpp) via
    // util/transcendental_eval.h ----

    bool transcendentals::exp_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
        return transcendental_eval::exp_taylor_bracket_at(xr, lo, hi);
    }

    bool transcendentals::log_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
        return transcendental_eval::log_taylor_bracket_at(xr, lo, hi);
    }

    bool transcendentals::atan_taylor_bracket_at(rational const& xr, rational& lo, rational& hi) {
        return transcendental_eval::atan_taylor_bracket_at(xr, lo, hi);
    }

    bool transcendentals::interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val) {
        return transcendental_eval::wide_interval_eval(op, lo, hi, lo_val, hi_val);
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

    // pi/2 and pi, each rounded outward (away from the true value) by more
    // than double's rounding error, so that using them as bounds never
    // excludes a value the corresponding function can actually attain (same
    // constants as nla::transcendentals::add_range_axioms). Used by
    // add_range_axioms (ASIN/ACOS) as well as add_atan2.
    static constexpr double k_pi_2_ub = 1.5707963267948968; // > true pi/2
    static constexpr double k_pi_ub   = 3.1415926535897936; // > true pi

    void transcendentals::add(transcendental_op_kind op, var arg, var val) {
        m_apps.push_back({ op, arg, val });
        m_retry.push_back(0);
        add_global_axioms(op, arg, val);
        add_range_axioms(op, val);
        find_and_add_identity_axiom(op, arg, val);
    }

    // Same tight, exact-rational two-sided bound as
    // nla::transcendentals::add_pi. A no-op if val is null_var or pi has
    // already been registered.
    void transcendentals::add_pi(var val) {
        if (val == null_var || m_pi_var != null_var)
            return;
        m_pi_var = val;
        rational lo("3.14159265358979");
        rational hi("3.14159265358980");
        literal lo_lit = ~bound_literal(s, val, atom::LT, lo); // val >= lo
        literal hi_lit = ~bound_literal(s, val, atom::GT, hi); // val <= hi
        s.mk_clause(1, &lo_lit, nullptr);
        s.mk_clause(1, &hi_lit, nullptr);
    }

    // Ported from nla::transcendentals::add_atan2: records the application
    // and asserts atan2's permanent range axiom (-pi <= val <= pi; k_pi_ub
    // is an outward-rounded rational upper bound for pi, so this is sound
    // even though the true range is the slightly tighter half-open
    // (-pi, pi]). A no-op if any of y, x, val is null_var.
    void transcendentals::add_atan2(var y, var x, var val) {
        if (y == null_var || x == null_var || val == null_var)
            return;
        m_atan2_apps.push_back({ y, x, val });
        m_retry_atan2.push_back(0);
        rational bnd = to_rational(k_pi_ub);
        literal lits[2] = {
            ~bound_literal(s, val, atom::GT, bnd),
            ~bound_literal(s, val, atom::LT, -bnd)
        };
        s.mk_clause(1, lits, nullptr);
        s.mk_clause(1, lits + 1, nullptr);
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
            break; // SIN/COS/ATAN/TAN/ASIN/ACOS/SINH/COSH/TANH/ASINH/ACOSH/ATANH:
                    // no exact global linear tangent bound; left to
                    // refine_app's Taylor sandwich / interval enclosure and
                    // (for the ops below) add_range_axioms' simple value bound.
        }
    }

    // pi/2 and pi, each rounded outward (away from the true value) by more
    // than double's rounding error, so that using them as bounds never
    // excludes a value the corresponding function can actually attain (same
    // constants as nla::transcendentals::add_range_axioms).

    // Exact, unconditional value-range bound, ported from
    // nla::transcendentals::add_range_axioms. Added once, permanently, the
    // moment the application is registered - these are true for the op's
    // *entire* range, so (like add_global_axioms) they need no
    // witness-dependent widening.
    void transcendentals::add_range_axioms(transcendental_op_kind op, var val) {
        switch (op) {
        case transcendental_op_kind::SIN:
        case transcendental_op_kind::COS: {
            auto lit1 = ~bound_literal(s, val, atom::GT, rational(1));
            s.mk_clause(1, &lit1, nullptr); // NOT(val > 1)
            auto lit2 = ~bound_literal(s, val, atom::LT, rational(-1));
            s.mk_clause(1, &lit2, nullptr); // NOT(val < -1)
            break;
        }
        case transcendental_op_kind::TANH: {
            literal lo = bound_literal(s, val, atom::GT, rational(-1)); // val > -1
            literal hi = bound_literal(s, val, atom::LT, rational(1));  // val < 1
            s.mk_clause(1, &lo, nullptr);
            s.mk_clause(1, &hi, nullptr);
            break;
        }
        case transcendental_op_kind::COSH: {
            literal lit = ~bound_literal(s, val, atom::LT, rational(1)); // NOT(val < 1), i.e. val >= 1
            s.mk_clause(1, &lit, nullptr);
            break;
        }
        case transcendental_op_kind::ACOSH: {
            literal lit = ~bound_literal(s, val, atom::LT, rational(0)); // val >= 0
            s.mk_clause(1, &lit, nullptr);
            break;
        }
        case transcendental_op_kind::ASIN: {
            rational bnd = to_rational(k_pi_2_ub);
            auto lit1 = ~bound_literal(s, val, atom::GT, bnd);
            s.mk_clause(1, &lit1, nullptr);
            auto lit2 = ~bound_literal(s, val, atom::LT, -bnd);
            s.mk_clause(1, &lit2, nullptr);
            break;
        }
        case transcendental_op_kind::ACOS: {
            rational bnd = to_rational(k_pi_ub);
            auto lit1 = ~bound_literal(s, val, atom::GT, bnd);
            s.mk_clause(1, &lit1, nullptr);
            auto lit2 = ~bound_literal(s, val, atom::LT, rational(0));
            s.mk_clause(1, &lit2, nullptr);
            break;
        }
        default:
            break; // TAN, ATAN, SINH, ASINH, ATANH, EXP, LOG: no simple unconditional
                    // value bound (EXP/LOG/ATAN already get a stronger, argument-
                    // relating bound from add_global_axioms/the Taylor sandwich).
        }
    }

    // Cross-application identity axiom: scans previously-registered
    // applications for one with the same argument variable and a
    // complementary op (ported from nla::transcendentals::add_transcendental's
    // pairing scan), and - if found - asserts the corresponding permanent
    // polynomial equality the moment the second application of the pair is
    // registered.
    void transcendentals::find_and_add_identity_axiom(transcendental_op_kind op, var arg, var val) {
        for (unsigned i = 0; i + 1 < m_apps.size(); ++i) {
            app const& other = m_apps[i];
            if (other.arg != arg)
                continue;
            if (op == transcendental_op_kind::SIN && other.op == transcendental_op_kind::COS)
                add_identity_axiom({ val, other.val }, true, false);
            else if (op == transcendental_op_kind::COS && other.op == transcendental_op_kind::SIN)
                add_identity_axiom({ other.val, val }, true, false);
            else if (op == transcendental_op_kind::SINH && other.op == transcendental_op_kind::COSH)
                add_identity_axiom({ other.val, val }, false, true);
            else if (op == transcendental_op_kind::COSH && other.op == transcendental_op_kind::SINH)
                add_identity_axiom({ val, other.val }, false, true);
            else if (op == transcendental_op_kind::TANH && other.op == transcendental_op_kind::COSH)
                add_identity_axiom({ other.val, val }, false, false);
            else if (op == transcendental_op_kind::COSH && other.op == transcendental_op_kind::TANH)
                add_identity_axiom({ val, other.val }, false, false);
        }
    }

    // Asserts the permanent polynomial equality for a matched pair (see
    // find_and_add_identity_axiom / nla::transcendentals's module comment):
    //   is_sin_cos:                v1^2 + v2^2 - 1 = 0        (v1=sin, v2=cos)
    //   is_cosh_sinh:              v1^2 - v2^2 - 1 = 0        (v1=cosh, v2=sinh)
    //   otherwise (cosh, tanh):    v1^2 - v1^2*v2^2 - 1 = 0   (v1=cosh, v2=tanh)
    // Each holds exactly for every real value of the shared argument, with
    // no remainder/error term, so - unlike the Taylor sandwich - it is
    // asserted unconditionally and permanently, the moment the pair is found.
    void transcendentals::add_identity_axiom(identity_pair const& pr, bool is_sin_cos, bool is_cosh_sinh) {
        auto& pm = s.pm();
        polynomial_ref v1(pm.mk_polynomial(pr.v1), pm);
        polynomial_ref v2(pm.mk_polynomial(pr.v2), pm);
        polynomial_ref v1sq(pm); v1sq = v1 * v1;
        polynomial_ref eq(pm);
        if (is_sin_cos) {
            polynomial_ref v2sq(pm); v2sq = v2 * v2;
            eq = v1sq + v2sq - rational(1);
        }
        else if (is_cosh_sinh) {
            polynomial_ref v2sq(pm); v2sq = v2 * v2;
            eq = v1sq - v2sq - rational(1);
        }
        else {
            polynomial_ref v2sq(pm); v2sq = v2 * v2;
            eq = v1sq - (v1sq * v2sq) - rational(1);
        }
        poly* pp = eq.get();
        bool is_even = false;
        literal lit = s.mk_ineq_literal(atom::EQ, 1, &pp, &is_even);
        s.mk_clause(1, &lit, nullptr);
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
        // SIN/COS are not monotonic on all of [xlo, xhi] (they can have an
        // extremum strictly inside it), so they instead go through
        // sin_cos_taylor_bracket, which combines the two endpoint brackets
        // the same way but additionally clamps to +-1 whenever a periodic
        // extremum might fall inside the interval (detected using a
        // verified rational bracket for pi, so it stays exact throughout).
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
            case transcendental_op_kind::SIN:
                have_exact = transcendental_eval::sin_cos_taylor_bracket(transcendental_eval::op_kind::SIN, xlo, xhi, rlo, rhi);
                break;
            case transcendental_op_kind::COS:
                have_exact = transcendental_eval::sin_cos_taylor_bracket(transcendental_eval::op_kind::COS, xlo, xhi, rlo, rhi);
                break;
            default:
                break; // remaining ops: use interval_eval's extremum-aware double enclosure instead.
            }
            if (have_exact && a.op != transcendental_op_kind::SIN && a.op != transcendental_op_kind::COS) {
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

    // atan2(y, x): the exact fact sign(val) == sign(y) whenever y != 0 (atan2's
    // quadrant selection never flips the sign of the result relative to y),
    // checked first (exact, no floating point involved); then a float-based
    // delta-check against std::atan2(y, x) with a widening box-exclusion
    // fallback lemma (a 2D analogue of refine_app's box-exclusion, since
    // atan2's branch cut near x<0,y~0 makes a closed-form enclosure like
    // interval_eval substantially more involved) - ported from
    // nla::transcendentals::check_atan2.
    bool transcendentals::refine_atan2(unsigned idx) {
        atan2_app const& a = m_atan2_apps[idx];
        anum const& yv = s.value(a.y);
        anum const& xv = s.value(a.x);
        anum const& vv = s.value(a.val);
        if (s.am().is_pos(yv) && !s.am().is_pos(vv)) {
            literal lits[2] = {
                ~bound_literal(s, a.y, atom::GT, rational(0)),  // y <= 0
                bound_literal(s, a.val, atom::GT, rational(0))  // val > 0
            };
            s.mk_clause(2, lits, nullptr);
            return true;
        }
        if (s.am().is_neg(yv) && !s.am().is_neg(vv)) {
            literal lits[2] = {
                ~bound_literal(s, a.y, atom::LT, rational(0)),  // y >= 0
                bound_literal(s, a.val, atom::LT, rational(0))  // val < 0
            };
            s.mk_clause(2, lits, nullptr);
            return true;
        }
        rational yl, yu, xl, xu, vl, vu;
        s.am().get_interval(yv, yl, yu, 64);
        s.am().get_interval(xv, xl, xu, 64);
        s.am().get_interval(vv, vl, vu, 64);
        double y = ((yl + yu) / rational(2)).get_double();
        double x = ((xl + xu) / rational(2)).get_double();
        double v = ((vl + vu) / rational(2)).get_double();
        double fv = std::atan2(y, x);
        if (!std::isfinite(fv))
            return false; // (0,0): undefined, not this check's responsibility.
        // Same generous margin as nla::transcendentals::check_atan2: atan2's
        // derivative is unbounded near the branch cut (x < 0, y ~ 0), so a
        // tight closed-form error bound is not attempted here.
        double err = 4096.0 * std::numeric_limits<double>::epsilon() * std::max(1.0, std::fabs(fv));
        if (std::fabs(v - fv) <= err)
            return false;
        // Widen the (possibly zero-width) y/x intervals before excluding
        // them, same rationale and exponential-retry growth as refine_app.
        rational ymid = (yl + yu) / rational(2); if (ymid.is_neg()) ymid = -ymid;
        rational xmid = (xl + xu) / rational(2); if (xmid.is_neg()) xmid = -xmid;
        rational scale = std::max(std::max(ymid, xmid), rational(1));
        rational growth = rational::power_of_two(std::min(m_retry_atan2[idx], 30u));
        rational rdelta = rational(1, 1000000) * scale * growth;
        rational ylo = yl - rdelta, yhi = yu + rdelta;
        rational xlo = xl - rdelta, xhi = xu + rdelta;
        rational rv = to_rational(v);
        literal_vector lemma;
        lemma.push_back(bound_literal(s, a.y, atom::LT, ylo));
        lemma.push_back(bound_literal(s, a.y, atom::GT, yhi));
        lemma.push_back(bound_literal(s, a.x, atom::LT, xlo));
        lemma.push_back(bound_literal(s, a.x, atom::GT, xhi));
        if (v < fv)
            lemma.push_back(~bound_literal(s, a.val, atom::LT, rv)); // val >= rv
        else
            lemma.push_back(~bound_literal(s, a.val, atom::GT, rv)); // val <= rv
        s.mk_clause(lemma.size(), lemma.data(), nullptr);
        ++m_retry_atan2[idx];
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
        for (unsigned i = 0; i < m_atan2_apps.size(); ++i)
            if (refine_atan2(i))
                added = true;
        if (refine_monotonicity())
            added = true;
        return added;
    }
}

