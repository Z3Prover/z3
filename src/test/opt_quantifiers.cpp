/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_quantifiers.cpp

Abstract:

    Tests for optimization under hard constraints that quantify over
    linear integer or linear real arithmetic (opt.elim_quantifiers_rlimit).
    Such constraints are replaced by equivalent quantifier-free ones, so
    the optimum is exact; constraints outside that fragment are kept.

Author:

    Lev Nachmanson 2026-10-30

--*/
#include "opt/opt_context.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"

static void set_elim_quantifiers_rlimit(opt::context& ctx, unsigned rlimit) {
    params_ref p;
    p.set_uint("elim_quantifiers_rlimit", rlimit);
    ctx.updt_params(p);
}

static bool is_value(arith_util& a, expr* e, int expected) {
    rational r;
    return a.is_numeral(e, r) && r == rational(expected);
}

// The single objective of ctx has the exact optimum expected, and the model
// attains it.
static void check_optimum(opt::context& ctx, expr* objective, int expected) {
    ast_manager& m = ctx.get_manager();
    arith_util a(m);
    expr_ref_vector asms(m);
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(is_value(a, ctx.get_lower(0), expected));
    ENSURE(is_value(a, ctx.get_upper(0), expected));
    model_ref mdl;
    ctx.get_model(mdl);
    ENSURE(mdl);
    ENSURE(is_value(a, (*mdl)(objective), expected));
}

static void tst_forall_real(unsigned rlimit) {
    // maximize x subject to forall y >= 0. x <= y + 1; the optimum is 1.
    std::cout << "opt_quantifiers: forall over the reals, rlimit " << rlimit << "\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_elim_quantifiers_rlimit(ctx, rlimit);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    sort* real = a.mk_real();
    symbol y_name("y");
    expr_ref y(m.mk_var(0, real), m);
    expr_ref body(m.mk_implies(a.mk_ge(y, a.mk_real(0)), a.mk_le(x, a.mk_add(y, a.mk_real(1)))), m);
    ctx.add_hard_constraint(m.mk_forall(1, &real, &y_name, body));
    ctx.add_objective(to_app(x.get()), true);
    if (rlimit > 0) {
        check_optimum(ctx, x, 1);
        return;
    }
    // Without elimination the arithmetic solver does not see the
    // quantified bound, and the optimum stays unknown.
    expr_ref_vector asms(m);
    ENSURE(ctx.optimize(asms) == l_undef);
}

static void tst_exists_real() {
    // maximize x subject to exists y. x <= 2 y and y <= 3; the optimum is 6.
    std::cout << "opt_quantifiers: exists over the reals\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    sort* real = a.mk_real();
    symbol y_name("y");
    expr_ref y(m.mk_var(0, real), m);
    expr_ref body(m.mk_and(a.mk_le(x, a.mk_mul(a.mk_real(2), y)), a.mk_le(y, a.mk_real(3))), m);
    ctx.add_hard_constraint(m.mk_exists(1, &real, &y_name, body));
    ctx.add_objective(to_app(x.get()), true);
    check_optimum(ctx, x, 6);
}

static void tst_window_int() {
    // Every window [y + n, y + k] of integers contains a multiple of 4
    // exactly when k - n >= 3. With 0 <= n, k <= 10, minimize k - n; the
    // optimum is 3.
    std::cout << "opt_quantifiers: forall exists over the integers\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref n(m.mk_const("n", a.mk_int()), m);
    expr_ref k(m.mk_const("k", a.mk_int()), m);
    sort* integer = a.mk_int();
    symbol y_name("y"), z_name("z");
    // Inside exists z the variable z has index 0 and y has index 1.
    expr_ref z(m.mk_var(0, integer), m);
    expr_ref y(m.mk_var(1, integer), m);
    expr_ref inner(m.mk_and(a.mk_le(a.mk_add(y, n), z),
                            a.mk_le(z, a.mk_add(y, k)),
                            m.mk_eq(a.mk_mod(z, a.mk_int(4)), a.mk_int(0))), m);
    expr_ref exists_z(m.mk_exists(1, &integer, &z_name, inner), m);
    ctx.add_hard_constraint(m.mk_forall(1, &integer, &y_name, exists_z));
    for (expr* v : { n.get(), k.get() }) {
        ctx.add_hard_constraint(a.mk_ge(v, a.mk_int(0)));
        ctx.add_hard_constraint(a.mk_le(v, a.mk_int(10)));
    }
    expr_ref width(a.mk_sub(k, n), m);
    ctx.add_objective(to_app(width.get()), false);
    check_optimum(ctx, width, 3);
}

static void tst_nonlinear_kept() {
    // forall y. y * y + 1 >= c * y is outside the linear fragment; the
    // constraint is kept, so the optimum 2 is not claimed.
    std::cout << "opt_quantifiers: nonlinear body is kept\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref c(m.mk_const("c", a.mk_real()), m);
    sort* real = a.mk_real();
    symbol y_name("y");
    expr_ref y(m.mk_var(0, real), m);
    expr_ref body(a.mk_ge(a.mk_add(a.mk_mul(y, y), a.mk_real(1)), a.mk_mul(c, y)), m);
    ctx.add_hard_constraint(m.mk_forall(1, &real, &y_name, body));
    ctx.add_objective(to_app(c.get()), true);
    expr_ref_vector asms(m);
    ENSURE(ctx.optimize(asms) != l_true);
}

void tst_opt_quantifiers() {
    tst_forall_real(1000000);
    tst_forall_real(0);
    tst_exists_real();
    tst_window_int();
    tst_nonlinear_kept();
}
