/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_nlsat.cpp

Abstract:

    Tests for opt::nlsat_opt, exact optimization of a real objective over
    nlsat cells. Covers the engine outcomes that the SMT-LIB regressions
    cannot reach directly: an objective whose feasible set is unbounded
    above (no upper hint), and an open supremum proven as an upper bound.

Author:

    Lev Nachmanson 2026-08-27

--*/
#include "opt/opt_nlsat.h"
#include "ast/reg_decl_plugins.h"

// maximize x s.t. x^2 <= 2 within [0, 2]: the optimum sqrt(2) is attained
// and reported as an irrational algebraic numeral with a rational bracket.
static void tst_attained() {
    std::cout << "opt_nlsat: attained\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_le(a.mk_mul(x, x), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    lbool r = opt.maximize(hard, x, rational(0), true, rational(2), 64, res);
    ENSURE(r == l_true);
    ENSURE(res.m_attained);
    ENSURE(res.m_model);
    ENSURE(a.is_irrational_algebraic_numeral(res.m_value));
    ENSURE(res.m_lower <= res.m_upper);
    ENSURE(res.m_lower < rational(141422, 100000));
    ENSURE(res.m_upper > rational(141421, 100000));
}

// maximize x s.t. x*y = 1 /\ y > 0 with no upper hint: the feasible set of
// the objective is unbounded above; the engine stops after a few unbounded
// rounds instead of spending the whole budget, with the best model so far.
static void tst_unbounded() {
    std::cout << "opt_nlsat: unbounded\n";
    ast_manager m;
    reg_decl_plugins(m);
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
    lbool r = opt.maximize(hard, x, rational(1), false, rational(0), 64, res);
    ENSURE(r == l_undef);
    ENSURE(!res.m_attained);
    ENSURE(!res.m_has_sup);
    ENSURE(res.m_model);
    ENSURE(res.m_rounds <= 8);
}

// maximize x s.t. x^2 < 2 within [0, 2] on a small round budget: the
// supremum sqrt(2) is not attained; after the budget is exhausted the
// engine proves it as an upper bound (prove_supremum).
static void tst_open_sup() {
    std::cout << "opt_nlsat: open supremum\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_lt(a.mk_mul(x, x), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    lbool r = opt.maximize(hard, x, rational(0), true, rational(2), 8, res);
    ENSURE(r == l_undef);
    ENSURE(!res.m_attained);
    ENSURE(res.m_model);
    ENSURE(res.m_has_sup);
    ENSURE(res.m_sup_upper >= rational(141421, 100000));
    ENSURE(res.m_sup_upper <= rational(15, 10));
    ENSURE(res.m_lower < res.m_sup_upper);
}

// maximize x s.t. x^3 = 2*x within [-2, 2]: the feasible set is the three
// isolated roots {-sqrt(2), 0, sqrt(2)} of the cubic, so every cell is a
// point; the maximum is the irrational root sqrt(2), attained and reported
// as an algebraic numeral.
static void tst_cubic_roots() {
    std::cout << "opt_nlsat: cubic roots\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(m.mk_eq(a.mk_mul(x, a.mk_mul(x, x)), a.mk_mul(two, x)));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    lbool r = opt.maximize(hard, x, rational(-2), true, rational(2), 64, res);
    ENSURE(r == l_true);
    ENSURE(res.m_attained);
    ENSURE(res.m_model);
    ENSURE(a.is_irrational_algebraic_numeral(res.m_value));
    ENSURE(res.m_lower <= res.m_upper);
    ENSURE(res.m_lower < rational(141422, 100000));
    ENSURE(res.m_upper > rational(141421, 100000));
}

// an uninterpreted function is outside the fragment: the engine declines
// without producing a model.
static void tst_outside_fragment() {
    std::cout << "opt_nlsat: outside fragment\n";
    ast_manager m;
    reg_decl_plugins(m);
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
    lbool r = opt.maximize(hard, x, rational(0), true, rational(2), 64, res);
    ENSURE(r == l_undef);
    ENSURE(!res.m_model);
    ENSURE(!res.m_attained);
}

// infeasible bracket: lo above the feasible set refutes the goal.
static void tst_infeasible() {
    std::cout << "opt_nlsat: infeasible\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector hard(m);
    hard.push_back(a.mk_le(a.mk_mul(x, x), two));
    params_ref p;
    opt::nlsat_opt opt(m, p);
    opt::nlsat_opt::result res(m);
    lbool r = opt.maximize(hard, x, rational(3), true, rational(4), 64, res);
    ENSURE(r == l_false);
    ENSURE(!res.m_model);
}

void tst_opt_nlsat() {
    tst_attained();
    tst_cubic_roots();
    tst_unbounded();
    tst_open_sup();
    tst_outside_fragment();
    tst_infeasible();
}
