/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_nlsat.cpp

Abstract:

    Tests for opt::nlsat_opt, exact optimization of a real objective over
    nlsat cells. Covers the engine outcomes that the SMT-LIB regressions
    cannot reach directly: an objective whose feasible set is unbounded
    above (no upper hint), and certification of a finite open supremum.

Author:

    Lev Nachmanson 2026-08-27

--*/
#include "opt/opt_nlsat.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/rlimit.h"
#include <initializer_list>

// Construct an exact root independently of the optimizer, optionally negated.
static expr_ref exact_root(ast_manager& m, int radicand, unsigned degree = 2, bool negate = false) {
    arith_util a(m);
    auto& am = a.am();
    scoped_anum value(am);
    am.set(value, radicand);
    am.root(value, degree, value);
    if (negate)
        am.neg(value);
    return expr_ref(a.mk_numeral(am, value, false), m);
}

// Decide ground arithmetic exactly, rather than comparing decimal displays.
static void ensure_exact(ast_manager& m, expr* fact, bool expected = true) {
    expr_ref simplified(fact, m);
    th_rewriter rw(m);
    rw(simplified);
    ENSURE(expected ? m.is_true(simplified) : m.is_false(simplified));
}

// The stored value and its rational bracket must describe a feasible model.
static void ensure_witness(ast_manager& m, expr_ref_vector const& hard, expr* obj,
                           rational const& lo, opt::nlsat_opt::result const& res) {
    ENSURE(res.m_model && res.m_value);
    expr_ref value(m);
    for (expr* f : hard) {
        ENSURE(res.m_model->eval_expr(f, value, true));
        ensure_exact(m, value);
    }
    ENSURE(res.m_model->eval_expr(obj, value, true));
    ensure_exact(m, m.mk_eq(value, res.m_value));
    arith_util a(m);
    ENSURE(res.m_lower <= res.m_upper);
    ensure_exact(m, a.mk_le(a.mk_numeral(lo, false), res.m_value));
    ensure_exact(m, a.mk_le(a.mk_numeral(res.m_lower, false), res.m_value));
    ensure_exact(m, a.mk_le(res.m_value, a.mk_numeral(res.m_upper, false)));
}

// maximize x s.t. x^2 <= 2 within [0, 2]: the optimum sqrt(2) is attained
// and reported as an irrational algebraic numeral with a rational bracket.
static void tst_attained() {
    std::cout << "opt_nlsat: attained\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_le(a.mk_mul(x, x), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    // Run the cell optimizer on the closed interval.
    lbool r = opt.maximize(hard, x, rational(0), rational(2), 64, res);
    ENSURE(r == l_true);
    ENSURE(res.m_attained);
    ENSURE(!res.m_unbounded && !res.m_has_sup && !res.m_open && !res.m_sup);
    ENSURE(a.is_irrational_algebraic_numeral(res.m_value));
    expr_ref expected = exact_root(m, 2);
    ensure_exact(m, m.mk_eq(res.m_value, expected));
    ensure_witness(m, hard, x, rational(0), res);
}

// maximize x s.t. x*y = 1 /\ y > 0 with no upper hint: the feasible set of
// the objective is unbounded above; after a few unbounded rounds the engine
// proves it by projecting a feasible ray, keeping the best model as a witness.
static void tst_unbounded() {
    std::cout << "opt_nlsat: unbounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_real()), m);
    expr_ref one(a.mk_numeral(rational(1), false), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref_vector hard(m);
    hard.push_back(m.mk_eq(a.mk_mul(x, y), one));
    hard.push_back(a.mk_gt(y, zero));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    // Run optimization without an upper hint so the unbounded proof is exercised.
    lbool r = opt.maximize(hard, x, rational(1), std::nullopt, 64, res);
    ENSURE(r == l_true);
    ENSURE(res.m_unbounded);
    ENSURE(!res.m_attained);
    ENSURE(!res.m_has_sup);
    ENSURE(!res.m_open && !res.m_sup);
    ensure_witness(m, hard, x, rational(1), res);
    ENSURE(res.m_rounds <= 8);
}

// Use prove_unbounded to prove unbounded for x in x*y = 1 /\ y > 0 (also in its
// division form x = 1/y, which purification must remove for nlsat), bounded
// above (l_false) for x^2 <= 2, and l_undef outside the fragment.
static void tst_prove_unbounded() {
    std::cout << "opt_nlsat: prove_unbounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    sort* real = a.mk_real();
    expr_ref x(m.mk_const(symbol("x"), real), m);
    expr_ref y(m.mk_const(symbol("y"), real), m);
    expr_ref one(a.mk_numeral(rational(1), false), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    params_ref p;
    opt::nlsat_opt opt(m, p);
    expr_ref_vector unbounded(m);
    unbounded.push_back(m.mk_eq(a.mk_mul(x, y), one));
    unbounded.push_back(a.mk_gt(y, zero));
    ENSURE(opt.prove_unbounded(unbounded, x, rational(1)) == l_true);
    expr_ref_vector division(m);
    division.push_back(m.mk_eq(x, a.mk_div(one, y)));
    division.push_back(a.mk_gt(y, zero));
    ENSURE(opt.prove_unbounded(division, x, rational(1)) == l_true);
    expr_ref_vector bounded(m);
    bounded.push_back(a.mk_le(a.mk_mul(x, x), two));
    ENSURE(opt.prove_unbounded(bounded, x, rational(0)) == l_false);
    func_decl_ref f(m.mk_func_decl(symbol("f"), real, real), m);
    expr_ref_vector outside(m);
    outside.push_back(a.mk_le(m.mk_app(f, x.get()), two));
    ENSURE(opt.prove_unbounded(outside, x, rational(0)) == l_undef);

    // Integer n > 0 and n^2 < 2 force n = 1, contradicting x*(n-1) = 1.
    // The real relaxation instead allows n to approach 1 from above.
    expr_ref n(m.mk_const(symbol("n"), a.mk_int()), m);
    expr_ref_vector mixed(m);
    mixed.push_back(m.mk_eq(a.mk_mul(x, a.mk_sub(a.mk_to_real(n), one)), one));
    mixed.push_back(a.mk_gt(n, a.mk_int(0)));
    mixed.push_back(a.mk_lt(a.mk_mul(n, n), a.mk_int(2)));
    ENSURE(opt.prove_unbounded(mixed, x, rational(0)) == l_undef);
}

// Maximize x with x^2 < 2: certify sqrt(2) as both a strict upper bound
// and an approachable limit, without replacing the feasible model by it.
static void tst_open_sup() {
    std::cout << "opt_nlsat: open supremum\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_lt(a.mk_mul(x, x), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    // Optimize for eight cell rounds, then certify the finite open limit.
    lbool r = opt.maximize(hard, x, rational(0), rational(2), 8, res);
    ENSURE(r == l_true);
    ENSURE(!res.m_attained);
    ENSURE(!res.m_unbounded);
    ENSURE(res.m_has_sup && res.m_open && res.m_sup);
    ENSURE(res.m_rounds == 8);
    expr_ref expected = exact_root(m, 2);
    ensure_exact(m, m.mk_eq(res.m_sup, expected));
    ensure_witness(m, hard, x, rational(0), res);
    ensure_exact(m, a.mk_lt(res.m_value, res.m_sup));
    ensure_exact(m, a.mk_le(a.mk_numeral(res.m_sup_lower, false), res.m_sup));
    ensure_exact(m, a.mk_le(res.m_sup, a.mk_numeral(res.m_sup_upper, false)));
}

// Approachability is separate from being an upper bound, and requires values
// strictly below the candidate even when the candidate itself is feasible.
static void tst_can_approach_from_below() {
    std::cout << "opt_nlsat: can_approach_from_below\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref zero(a.mk_real(0), m), one(a.mk_real(1), m), two(a.mk_real(2), m);
    expr_ref root = exact_root(m, 2);
    params_ref p;
    opt::nlsat_opt opt(m, p);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_lt(a.mk_mul(x, x), two));
    // The algebraic limit is approachable; the lo cutoff remains part of the query.
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), root) == l_true);
    ENSURE(opt.can_approach_from_below(hard, x, rational(2), root) == l_false);
    // A loose upper bound has a gap below it and is not approachable.
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), two) == l_false);
    // The interior value 1 is approachable but is not an upper bound: 5/4 is feasible.
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), one) == l_true);
    expr_ref above(a.mk_real(rational(5, 4)), m);
    ensure_exact(m, a.mk_gt(above, one));
    ensure_exact(m, a.mk_lt(a.mk_mul(above, above), two));

    expr_ref_vector rational_limit(m);
    rational_limit.push_back(a.mk_lt(a.mk_mul(x, x), a.mk_real(4)));
    ENSURE(opt.can_approach_from_below(rational_limit, x, rational(0), two) == l_true);

    expr_ref negative_root = exact_root(m, 2, 2, true);
    expr_ref_vector negative(m);
    negative.push_back(a.mk_gt(a.mk_mul(x, x), two));
    negative.push_back(a.mk_lt(x, zero));
    ENSURE(opt.can_approach_from_below(negative, x, rational(-2), negative_root) == l_true);

    // An isolated feasible root is attained, but no feasible values approach it.
    expr_ref_vector isolated(m);
    isolated.push_back(m.mk_eq(a.mk_mul(x, x), two));
    isolated.push_back(a.mk_gt(x, zero));
    ENSURE(opt.can_approach_from_below(isolated, x, rational(0), root) == l_false);
}

static void tst_projected_limits() {
    std::cout << "opt_nlsat: projected limits with moving witnesses\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_real()), m);
    expr_ref one(a.mk_real(1), m), zero(a.mk_real(0), m), two(a.mk_real(2), m);
    params_ref p;
    opt::nlsat_opt opt(m, p);
    expr_ref_vector hard(m);
    hard.push_back(m.mk_eq(a.mk_mul(a.mk_sub(one, x), y), one));
    hard.push_back(a.mk_gt(y, zero));
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), one) == l_true);
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), two) == l_false);
    ENSURE(opt.prove_unbounded(hard, x, rational(0)) == l_false);

    // The disconnected point must not prevent discovering the separate feasible ray.
    expr_ref point(m.mk_eq(x, zero), m);
    expr_ref ray(m.mk_and(m.mk_eq(a.mk_mul(x, y), one), a.mk_gt(y, zero)), m);
    hard.reset();
    hard.push_back(m.mk_or(point, ray));
    ENSURE(opt.prove_unbounded(hard, x, rational(0)) == l_true);
    ENSURE(opt.can_approach_from_below(hard, x, rational(-1), zero) == l_false);
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), two) == l_true);
}

// The shared equality encoding must select one root, not just its polynomial.
static void tst_algebraic_eq() {
    std::cout << "opt_nlsat: exact algebraic equality\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref q(a.mk_real(rational(-3, 2)), m), other(a.mk_real(2), m);
    ensure_exact(m, opt::mk_algebraic_eq(m, q, q));
    ensure_exact(m, opt::mk_algebraic_eq(m, other, q), false);

    // The four conjugates +/-sqrt(2 +/- sqrt(3)) share x^4 - 4*x^2 + 1.
    auto& am = a.am();
    scoped_anum two(am), sqrt3(am), inner(am), outer(am);
    am.set(two, 2);
    am.set(sqrt3, 3);
    am.root(sqrt3, 2, sqrt3);
    expr_ref_vector roots(m);
    for (bool plus : {false, true}) {
        if (plus)
            am.add(two, sqrt3, inner);
        else
            am.sub(two, sqrt3, inner);
        am.root(inner, 2, outer);
        roots.push_back(a.mk_numeral(am, outer, false));
        am.neg(outer);
        roots.push_back(a.mk_numeral(am, outer, false));
    }
    for (unsigned i = 0; i < roots.size(); ++i) {
        ENSURE(a.is_irrational_algebraic_numeral(roots.get(i)));
        for (unsigned j = 0; j < roots.size(); ++j)
            ensure_exact(m, opt::mk_algebraic_eq(m, roots.get(i), roots.get(j)), i == j);
    }
}

// Disabling or exhausting only the extra proof keeps the upper-bound proof
// and feasible witness; retrying with a full budget must still succeed.
static void tst_open_proof_budget() {
    std::cout << "opt_nlsat: open proof budget\n";
    for (unsigned proof_budget : {0u, 1u}) {
        ast_manager m;
        reg_decl_plugins(m);
        scoped_rlimit budget(m.limit(), 1000000);
        arith_util a(m);
        expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
        expr_ref_vector hard(m);
        hard.push_back(a.mk_lt(a.mk_mul(x, x), a.mk_real(2)));
        expr_ref expected = exact_root(m, 2);
        params_ref p;
        opt::nlsat_opt opt(m, p);
        opt::nlsat_opt::result res(m);
        // Optimize normally, but disable or exhaust finite-limit certification.
        ENSURE(opt.maximize(hard, x, rational(0), rational(2), 8, res, proof_budget) == l_undef);
        ENSURE(res.m_has_sup && res.m_sup);
        ENSURE(!res.m_attained && !res.m_unbounded && !res.m_open);
        ENSURE(res.m_rounds == 8);
        ensure_exact(m, m.mk_eq(res.m_sup, expected));
        ensure_witness(m, hard, x, rational(0), res);
        ensure_exact(m, a.mk_lt(res.m_value, res.m_sup));
        ENSURE(m.inc());
        // Re-run optimization after the private proof budget has been popped.
        ENSURE(opt.maximize(hard, x, rational(0), rational(2), 8, res) == l_true);
        ENSURE(res.m_open && res.m_has_sup && !res.m_attained && !res.m_unbounded);
        ensure_exact(m, m.mk_eq(res.m_sup, expected));
        ensure_witness(m, hard, x, rational(0), res);
        ensure_exact(m, a.mk_lt(res.m_value, res.m_sup));
    }
}

// Alternate open and attained inputs and check the result flags and limit.
// Explicit reset clears both numeral values and the model.
static void tst_result_reuse() {
    std::cout << "opt_nlsat: result reuse and reset\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref square(a.mk_mul(x, x), m), two(a.mk_real(2), m);
    expr_ref expected = exact_root(m, 2);
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    for (bool strict : {true, false, true}) {
        expr_ref_vector hard(m);
        hard.push_back(strict ? a.mk_lt(square, two) : a.mk_le(square, two));
        // Optimize again into the same result, alternating open and closed inputs.
        ENSURE(opt.maximize(hard, x, rational(0), rational(2), 8, res) == l_true);
        ENSURE(res.m_open == strict && res.m_has_sup == strict);
        ENSURE(res.m_attained == !strict && !res.m_unbounded);
        ENSURE(strict ? res.m_sup.get() != nullptr : res.m_sup.get() == nullptr);
        ensure_exact(m, m.mk_eq(strict ? res.m_sup.get() : res.m_value.get(), expected));
        ensure_witness(m, hard, x, rational(0), res);
        if (strict)
            ensure_exact(m, a.mk_lt(res.m_value, res.m_sup));
    }
    res.reset();
    ENSURE(!res.m_value && !res.m_sup && !res.m_model);
    ENSURE(!res.m_attained && !res.m_unbounded && !res.m_has_sup && !res.m_open);
    ENSURE(res.m_rounds == 0);
}

// Integer variables, UF applications, and nonnumeral candidates must not be
// accepted by the real-arithmetic approachability certificate.
static void tst_approach_outside_fragment() {
    std::cout << "opt_nlsat: approachability outside fragment\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref n(m.mk_const(symbol("n"), a.mk_int()), m);
    expr_ref two(a.mk_real(2), m);
    params_ref p;
    opt::nlsat_opt opt(m, p);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_lt(a.mk_mul(x, x), two));
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), x) == l_undef);
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), nullptr) == l_undef);

    func_decl_ref f(m.mk_func_decl(symbol("f"), a.mk_real(), a.mk_real()), m);
    expr_ref fx(m.mk_app(f, x.get()), m);
    ENSURE(opt.can_approach_from_below(hard, fx, rational(0), two) == l_undef);
    hard.push_back(a.mk_lt(fx, two));
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), two) == l_undef);

    // Relaxing n to a real would incorrectly make 2 approachable; integer n < 2 cannot.
    expr_ref_vector mixed(m);
    mixed.push_back(a.mk_lt(x, a.mk_to_real(n)));
    mixed.push_back(a.mk_lt(n, a.mk_int(2)));
    mixed.push_back(a.mk_lt(a.mk_mul(x, x), a.mk_real(4)));
    ENSURE(opt.can_approach_from_below(mixed, x, rational(0), two) == l_undef);
    ENSURE(opt.can_approach_from_below(mixed, n, rational(0), two) == l_undef);
}

// Private proof budgets may expire, but must not disable enclosing limits
// or swallow cancellation. Use resource ticks rather than asynchronous timers.
static void tst_approach_resource_scopes() {
    std::cout << "opt_nlsat: approachability resource scopes\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref root = exact_root(m, 2);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_lt(a.mk_mul(x, x), a.mk_real(2)));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    uint64_t start = m.limit().count();
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), root, 0) == l_undef);
    ENSURE(m.limit().count() == start);
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), root, 1) == l_undef);
    ENSURE(m.inc());
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), root) == l_true);
    {
        scoped_rlimit enclosing(m.limit(), 1);
        ENSURE(opt.can_approach_from_below(hard, x, rational(0), root) == l_undef);
        // pop clamps the count to the ceiling; the next tick must still fail.
        ENSURE(!m.inc());
    }
    ENSURE(m.inc());
    m.limit().cancel();
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), root) == l_undef);
    ENSURE(m.limit().is_canceled());
    m.limit().reset_cancel();
    ENSURE(opt.can_approach_from_below(hard, x, rational(0), root) == l_true);
}

// maximize x s.t. x^3 = 2*x within [-2, 2]: the feasible set is the three
// isolated roots {-sqrt(2), 0, sqrt(2)} of the cubic, so every cell is a
// point; the maximum is the irrational root sqrt(2), attained and reported
// as an algebraic numeral.
static void tst_cubic_roots() {
    std::cout << "opt_nlsat: cubic roots\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(m.mk_eq(a.mk_mul(x, a.mk_mul(x, x)), a.mk_mul(two, x)));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    // Optimize over the three isolated roots, rather than over an open cell.
    lbool r = opt.maximize(hard, x, rational(-2), rational(2), 64, res);
    ENSURE(r == l_true);
    ENSURE(res.m_attained);
    ENSURE(!res.m_unbounded && !res.m_has_sup && !res.m_open && !res.m_sup);
    ENSURE(a.is_irrational_algebraic_numeral(res.m_value));
    expr_ref expected = exact_root(m, 2);
    ensure_exact(m, m.mk_eq(res.m_value, expected));
    ensure_witness(m, hard, x, rational(-2), res);
}

// an uninterpreted function is outside the fragment: the engine declines
// without producing a model.
static void tst_outside_fragment() {
    std::cout << "opt_nlsat: outside fragment\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    sort* real = a.mk_real();
    expr_ref x(m.mk_const(symbol("x"), real), m);
    func_decl_ref f(m.mk_func_decl(symbol("f"), real, real), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_le(a.mk_mul(x, x), two));
    hard.push_back(a.mk_le(m.mk_app(f, x.get()), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    // Optimization must decline the UF problem without claiming a certificate.
    lbool r = opt.maximize(hard, x, rational(0), rational(2), 64, res);
    ENSURE(r == l_undef);
    ENSURE(!res.m_model);
    ENSURE(!res.m_attained);
    ENSURE(!res.m_value && !res.m_sup && !res.m_has_sup && !res.m_open && !res.m_unbounded);
}

// infeasible bracket: lo above the feasible set refutes the goal.
static void tst_infeasible() {
    std::cout << "opt_nlsat: infeasible\n";
    ast_manager m;
    reg_decl_plugins(m);
    scoped_rlimit budget(m.limit(), 1000000);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_le(a.mk_mul(x, x), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    // Optimization must refute the infeasible bracket, not report an open optimum.
    lbool r = opt.maximize(hard, x, rational(3), rational(4), 64, res);
    ENSURE(r == l_false);
    ENSURE(!res.m_model);
    ENSURE(!res.m_value && !res.m_sup && !res.m_attained && !res.m_has_sup && !res.m_open && !res.m_unbounded);
}

// Run the cell optimizer and its bounded certificate regressions.
void tst_opt_nlsat() {
    tst_attained();
    tst_cubic_roots();
    tst_unbounded();
    tst_prove_unbounded();
    tst_open_sup();
    tst_can_approach_from_below();
    tst_projected_limits();
    tst_algebraic_eq();
    tst_open_proof_budget();
    tst_result_reuse();
    tst_approach_outside_fragment();
    tst_approach_resource_scopes();
    tst_outside_fragment();
    tst_infeasible();
}
