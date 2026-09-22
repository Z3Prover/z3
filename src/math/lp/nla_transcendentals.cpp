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

    void transcendentals::add_transcendental(nlsat::transcendental_op_kind op, lpvar arg, lpvar val) {
        if (arg == null_lpvar || val == null_lpvar)
            return;
        app a{ op, arg, val };
        m_apps.push_back(a);
        m_core.trail().push(push_back_vector(m_apps));
        add_range_axioms(op, val);
        // Cross-application identity axioms (sin^2+cos^2=1 etc.) are no
        // longer tracked here: nra_solver forwards this application
        // straight to nlsat (register_transcendentals_with_nlsat), and
        // nlsat::transcendentals::add already discovers matching pairs and
        // asserts the identity itself - see the module comment.
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

    void transcendentals::add_range_axioms(nlsat::transcendental_op_kind op, lpvar val) {
        auto& lra = m_core.lra;
        switch (op) {
        case nlsat::transcendental_op_kind::SIN:
        case nlsat::transcendental_op_kind::COS:
            lra.add_var_bound(val, lp::lconstraint_kind::LE, rational(1));
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(-1));
            break;
        case nlsat::transcendental_op_kind::TANH:
            lra.add_var_bound(val, lp::lconstraint_kind::LT, rational(1));
            lra.add_var_bound(val, lp::lconstraint_kind::GT, rational(-1));
            break;
        case nlsat::transcendental_op_kind::COSH:
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(1));
            break;
        case nlsat::transcendental_op_kind::ACOSH:
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(0));
            break;
        case nlsat::transcendental_op_kind::ASIN:
            lra.add_var_bound(val, lp::lconstraint_kind::LE, to_rational(k_pi_2_ub));
            lra.add_var_bound(val, lp::lconstraint_kind::GE, to_rational(-k_pi_2_ub));
            break;
        case nlsat::transcendental_op_kind::ATAN:
            lra.add_var_bound(val, lp::lconstraint_kind::LT, to_rational(k_pi_2_ub));
            lra.add_var_bound(val, lp::lconstraint_kind::GT, to_rational(-k_pi_2_ub));
            break;
        case nlsat::transcendental_op_kind::ACOS:
            lra.add_var_bound(val, lp::lconstraint_kind::LE, to_rational(k_pi_ub));
            lra.add_var_bound(val, lp::lconstraint_kind::GE, rational(0));
            break;
        case nlsat::transcendental_op_kind::EXP:
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

    char const* transcendentals::op_name(nlsat::transcendental_op_kind op) {
        return nlsat::transcendental_eval::op_name(op);
    }

    double transcendentals::eval(nlsat::transcendental_op_kind op, double x) {
        return nlsat::transcendental_eval::eval(op, x);
    }

    // A conservative (not tight) additive error bound accounting for the
    // floating point round-off incurred by evaluating op in double
    // precision. See nlsat::transcendental_eval::error_bound (nlsat/transcendental_eval.cpp)
    // for the shared implementation.
    double transcendentals::error_bound(nlsat::transcendental_op_kind op, double x, double fx) {
        return nlsat::transcendental_eval::error_bound(op, x, fx);
    }

    // Exact rational equal to the finite double d; see
    // nlsat::transcendental_eval::to_rational for the shared implementation.
    rational transcendentals::to_rational(double d) {
        return nlsat::transcendental_eval::to_rational(d);
    }

    bool transcendentals::has_linear_majorant(nlsat::transcendental_op_kind op) {
        switch (op) {
        case nlsat::transcendental_op_kind::SIN:
        case nlsat::transcendental_op_kind::TANH:
        case nlsat::transcendental_op_kind::ATAN:
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
        if (a.op != nlsat::transcendental_op_kind::SIN && a.op != nlsat::transcendental_op_kind::COS)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        rational const& pr = c.val(m_pi_var);

        if (a.op == nlsat::transcendental_op_kind::SIN) {
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
        if (a.op != nlsat::transcendental_op_kind::EXP)
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
        if (a.op != nlsat::transcendental_op_kind::EXP)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        rational const& yr = c.val(a.val);
        for (auto const& other : m_apps) {
            if (other.op != nlsat::transcendental_op_kind::EXP || other.arg == a.arg)
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

    bool transcendentals::check_log_upper_bound(app& a) {
        if (a.op != nlsat::transcendental_op_kind::LOG)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        if (!xr.is_pos())
            return false; // outside log's domain; not this check's responsibility
        rational const& yr = c.val(a.val);
        if (yr <= xr - 1)
            return false; // log(x) <= x-1 already holds, nothing to do.
        // val - arg <= -1, i.e. val <= arg - 1; sound for every x > 0
        // (tangent line at x=1 - log is concave, so every tangent line is
        // a global upper bound over the domain - the dual, via t=log(x),
        // of check_exp_lower_bound's exp(t) >= 1+t). Guarded by arg > 0
        // since (unlike exp) log's domain is not all reals.
        lp::lar_term diff(rational(1), a.val, rational(-1), a.arg); // val - arg
        lemma_builder lemma(c, "transcendental log upper bound: arg non-positive or log(arg) <= arg-1");
        lemma |= ineq(a.arg, lp::lconstraint_kind::LE, rational(0));
        lemma |= ineq(diff, lp::lconstraint_kind::LE, rational(-1));
        ++c.lp_settings().stats().m_nla_transcendental_splits;
        return true;
    }

    bool transcendentals::check_log_monotonicity(app& a) {
        if (a.op != nlsat::transcendental_op_kind::LOG)
            return false;
        core& c = m_core;
        rational const& xr = c.val(a.arg);
        if (!xr.is_pos())
            return false; // out of domain; not this check's responsibility
        rational const& yr = c.val(a.val);
        for (auto const& other : m_apps) {
            if (other.op != nlsat::transcendental_op_kind::LOG || other.arg == a.arg)
                continue;
            rational const& xr2 = c.val(other.arg);
            if (!xr2.is_pos())
                continue; // out of domain for the other application
            rational const& yr2 = c.val(other.val);
            // Monotonicity: 0 < x1 < x2 => log(x1) < log(x2). Guarded by
            // both arguments being positive (mirrors check_exp_monotonicity,
            // but log's domain restriction means the lemma must additionally
            // concede when either argument is non-positive).
            lp::lar_term arg_diff(rational(1), a.arg, rational(-1), other.arg); // a.arg - other.arg
            lp::lar_term val_diff(rational(1), a.val, rational(-1), other.val); // a.val - other.val
            if (xr < xr2 && yr >= yr2) {
                lemma_builder lemma(c, "transcendental log monotonicity");
                lemma |= ineq(a.arg, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(other.arg, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(arg_diff, lp::lconstraint_kind::GE, rational(0));
                lemma |= ineq(val_diff, lp::lconstraint_kind::LT, rational(0));
                ++c.lp_settings().stats().m_nla_transcendental_splits;
                return true;
            }
            if (xr > xr2 && yr <= yr2) {
                lemma_builder lemma(c, "transcendental log monotonicity");
                lemma |= ineq(a.arg, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(other.arg, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(arg_diff, lp::lconstraint_kind::LE, rational(0));
                lemma |= ineq(val_diff, lp::lconstraint_kind::GT, rational(0));
                ++c.lp_settings().stats().m_nla_transcendental_splits;
                return true;
            }
        }
        return false;
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
        if (check_exp_monotonicity(a))
            return true;
        if (check_log_upper_bound(a))
            return true;
        if (check_log_monotonicity(a))
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

        // A genuine delta-check failure. Rather than constructing our own
        // reactive polynomial/box-exclusion lemma here - a floating point
        // sampling process that can nudge the LP assignment indefinitely
        // without ever producing a certificate (see the module comment) -
        // just record that a failure was observed and let nlsat settle the
        // application exactly: should_run_bounded_nlsat(), gated on
        // has_observed_failure(), hands the problem to nra_solver/nlsat,
        // whose own nlsat_transcendentals engine refines the polynomial
        // constraints for arg/val internally (see nlsat_transcendentals.*).
        ++m_num_failures;
        TRACE(nla_solver, tout << op_name(a.op) << "(" << xr << ") = " << yr
                               << " but floating point evaluation gives " << fx
                               << " +/- " << err << "\n";);
        return false;
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

    // Sanity-checks nra_solver's (nlsat's) own model against the plain
    // delta-tolerance used by check_app, reading the actual algebraic
    // witness (via core::nra_model_bound) rather than the stale plain-LP
    // core::val. nlsat_transcendentals already refines each application's
    // polynomial constraints exactly before nlsat reports l_true, so this
    // is expected to always pass; it remains as a defensive check rather
    // than being trusted unconditionally.
    bool transcendentals::check_nra_model() {
        core& c = m_core;
        if (!c.use_nra_model())
            return false;
        double tolerance = c.params().arith_nl_transcendental_tolerance();
        for (auto const& a : m_apps) {
            rational xlo, xhi, ylo, yhi;
            c.nra_model_bound(a.arg, xlo, xhi);
            c.nra_model_bound(a.val, ylo, yhi);
            double x = ((xlo + xhi) / 2).get_double();
            double y = ((ylo + yhi) / 2).get_double();
            double fx = eval(a.op, x);
            if (!std::isfinite(fx))
                continue; // outside op's domain: not this check's responsibility.
            double err = error_bound(a.op, x, fx) + tolerance;
            if (std::fabs(y - fx) > err)
                return false;
        }
        return true;
    }
}
