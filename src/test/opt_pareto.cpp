/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_pareto.cpp

Abstract:

    Tests for Pareto enumeration in opt::context over the nlsat-backed
    solver (opt.pareto_nlsat). Covers what the SMT-LIB regressions cannot
    assert directly: the model values of the front points are irrational
    algebraic numerals, front points closer than the 12-digit display
    bracket are still told apart, and problems outside the NRA fragment
    fall back to the smt solver and enumerate their front there.

Author:

    Lev Nachmanson 2026-09-04

--*/
#include "opt/opt_context.h"
#include "ast/reg_decl_plugins.h"

static void set_pareto_priority(opt::context& ctx) {
    params_ref p;
    p.set_sym("priority", symbol("pareto"));
    ctx.updt_params(p);
}

// maximize x, maximize y s.t. x^2 = 2, y = -x: the front is the two
// incomparable points (sqrt(2), -sqrt(2)) and (-sqrt(2), sqrt(2)); the
// third round is unsat and the model values are algebraic numerals.
static void tst_irrational_front() {
    std::cout << "opt_pareto: irrational front\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    ctx.add_hard_constraint(m.mk_eq(a.mk_mul(x, x), two));
    ctx.add_hard_constraint(m.mk_eq(y, a.mk_uminus(x)));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(y.get()), true);
    expr_ref_vector asms(m);
    model_ref mdl;
    ENSURE(ctx.optimize(asms) == l_true);
    ctx.get_model(mdl);
    expr_ref x1 = (*mdl)(x);
    ENSURE(a.is_irrational_algebraic_numeral(x1));
    ENSURE(ctx.optimize(asms) == l_true);
    ctx.get_model(mdl);
    expr_ref x2 = (*mdl)(x);
    ENSURE(a.is_irrational_algebraic_numeral(x2));
    ENSURE(x1 != x2);
    ENSURE(ctx.optimize(asms) == l_false);
}

// two incomparable points whose coordinates differ by 10^-14, below the
// 12-digit bracket of the rounded comparison: (sqrt(2), sqrt(3) - 10^-14)
// and (sqrt(2) - 10^-14, sqrt(3)). The exact dominance constraints tell
// them apart, so both are enumerated before the front is exhausted.
static void tst_nearly_tied_front() {
    std::cout << "opt_pareto: nearly tied front\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx);
    sort* real = a.mk_real();
    expr_ref x(m.mk_const(symbol("x"), real), m);
    expr_ref w(m.mk_const(symbol("w"), real), m);
    expr_ref r2(m.mk_const(symbol("r2"), real), m);
    expr_ref r3(m.mk_const(symbol("r3"), real), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref three(a.mk_numeral(rational(3), false), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref eps(a.mk_numeral(rational(1, 100000000000000ull), false), m);
    ctx.add_hard_constraint(m.mk_eq(a.mk_mul(r2, r2), two));
    ctx.add_hard_constraint(a.mk_gt(r2, zero));
    ctx.add_hard_constraint(m.mk_eq(a.mk_mul(r3, r3), three));
    ctx.add_hard_constraint(a.mk_gt(r3, zero));
    expr_ref pt1(m.mk_and(m.mk_eq(x, r2), m.mk_eq(w, a.mk_sub(r3, eps))), m);
    expr_ref pt2(m.mk_and(m.mk_eq(x, a.mk_sub(r2, eps)), m.mk_eq(w, r3)), m);
    ctx.add_hard_constraint(m.mk_or(pt1, pt2));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(w.get()), true);
    expr_ref_vector asms(m);
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(ctx.optimize(asms) == l_false);
}

// an uninterpreted function puts the problem outside the NRA fragment: the
// loop falls back to the smt solver and still enumerates the (rational)
// two-point front.
static void tst_uf_fallback() {
    std::cout << "opt_pareto: uf fallback\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx);
    sort* real = a.mk_real();
    expr_ref x(m.mk_const(symbol("x"), real), m);
    expr_ref w(m.mk_const(symbol("w"), real), m);
    func_decl_ref f(m.mk_func_decl(symbol("f"), real, real), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref one(a.mk_numeral(rational(1), false), m);
    expr_ref pt1(m.mk_and(m.mk_eq(x, one), m.mk_eq(w, zero)), m);
    expr_ref pt2(m.mk_and(m.mk_eq(x, zero), m.mk_eq(w, one)), m);
    ctx.add_hard_constraint(m.mk_or(pt1, pt2));
    ctx.add_hard_constraint(a.mk_ge(m.mk_app(f, x.get()), zero));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(w.get()), true);
    expr_ref_vector asms(m);
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(ctx.optimize(asms) == l_false);
}

void tst_opt_pareto() {
    tst_irrational_front();
    tst_nearly_tied_front();
    tst_uf_fallback();
}
