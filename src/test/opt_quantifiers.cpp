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
    // quantified bound; whatever it answers must not contradict it.
    expr_ref_vector asms(m);
    lbool r = ctx.optimize(asms);
    ENSURE(r != l_false);
    if (r == l_true)
        ENSURE(is_value(a, ctx.get_upper(0), 1));
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
    // The second check-sat reuses the remembered elimination.
    check_optimum(ctx, width, 3);
}

static void tst_negative_divisor() {
    // With 0 <= x <= 10, exists z. 0 <= z <= x and (mod z -3) = 0 holds
    // for every x (take z = 0), so the maximum of x is 10. The qe tactic
    // alone turns the constraint into false.
    std::cout << "opt_quantifiers: mod by a negative numeral\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref x(m.mk_const("x", a.mk_int()), m);
    sort* integer = a.mk_int();
    symbol z_name("z");
    expr_ref z(m.mk_var(0, integer), m);
    expr_ref body(m.mk_and(a.mk_le(a.mk_int(0), z), a.mk_le(z, x),
                           m.mk_eq(a.mk_mod(z, a.mk_int(-3)), a.mk_int(0))), m);
    ctx.add_hard_constraint(m.mk_exists(1, &integer, &z_name, body));
    ctx.add_hard_constraint(a.mk_ge(x, a.mk_int(0)));
    ctx.add_hard_constraint(a.mk_le(x, a.mk_int(10)));
    ctx.add_objective(to_app(x.get()), true);
    check_optimum(ctx, x, 10);
}

static void tst_positive_divisor_offset() {
    // With 0 <= a <= 5: exists y0 in [-3, a + 3]. forall y1 in [-3, a + 3].
    // (mod (y0 - 1) 3) != y1 + 2 a + 13. The right side is at least 10
    // and mod is at most 2, so the constraint holds and the maximum of a
    // is 5. The qe tactic alone turns the constraint into false.
    std::cout << "opt_quantifiers: mod with an offset\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref c(m.mk_const("a", a.mk_int()), m);
    sort* integer = a.mk_int();
    symbol y0_name("y0"), y1_name("y1");
    expr_ref upper(a.mk_add(c, a.mk_int(3)), m);
    // Inside forall y1 the variable y1 has index 0 and y0 has index 1.
    expr_ref y1(m.mk_var(0, integer), m);
    expr_ref y0_inner(m.mk_var(1, integer), m);
    expr_ref lhs(a.mk_mod(a.mk_add(y0_inner, a.mk_int(-1)), a.mk_int(3)), m);
    expr_ref rhs(a.mk_add(y1, a.mk_mul(a.mk_int(2), c), a.mk_int(13)), m);
    expr_ref y1_range(m.mk_and(a.mk_le(a.mk_int(-3), y1), a.mk_le(y1, upper)), m);
    expr_ref forall_y1(m.mk_forall(1, &integer, &y1_name, m.mk_implies(y1_range, m.mk_not(m.mk_eq(lhs, rhs)))), m);
    expr_ref y0(m.mk_var(0, integer), m);
    expr_ref y0_range(m.mk_and(a.mk_le(a.mk_int(-3), y0), a.mk_le(y0, upper)), m);
    ctx.add_hard_constraint(m.mk_exists(1, &integer, &y0_name, m.mk_and(y0_range, forall_y1)));
    ctx.add_hard_constraint(a.mk_ge(c, a.mk_int(0)));
    ctx.add_hard_constraint(a.mk_le(c, a.mk_int(5)));
    ctx.add_objective(to_app(c.get()), true);
    check_optimum(ctx, c, 5);
}

static void tst_negated_coefficient() {
    // maximize x subject to forall y >= 0. x + (* (- 1) y) <= 7; the
    // coefficient (- 1) is folded into the numeral -1, and the optimum is 7.
    std::cout << "opt_quantifiers: coefficient written as (- 1)\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    sort* real = a.mk_real();
    symbol y_name("y");
    expr_ref y(m.mk_var(0, real), m);
    expr_ref minus_y(a.mk_mul(a.mk_uminus(a.mk_real(1)), y), m);
    expr_ref body(m.mk_implies(a.mk_ge(y, a.mk_real(0)), a.mk_le(a.mk_add(x, minus_y), a.mk_real(7))), m);
    ctx.add_hard_constraint(m.mk_forall(1, &real, &y_name, body));
    ctx.add_objective(to_app(x.get()), true);
    check_optimum(ctx, x, 7);
}

static void tst_qe_disagrees() {
    // With -4 <= a, b <= 4: exists y, q, r2, q3, r. 0 <= y <= 1 and
    // a + 3 = 6 q + r2, 0 <= r2 < 6 and q + 2 a = 3 q3 + r, 0 <= r < 3 and
    // r + 3 b <= 5. a = b = -4 satisfies it (q = -1, r2 = 5, q3 = -3,
    // r = 0), so the minimum of a + b is -8. The qe tactic alone drops
    // a = -4; its result differs from that of qe_rec, so the constraint
    // is kept.
    std::cout << "opt_quantifiers: qe and qe_rec disagree\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    expr_ref ca(m.mk_const("a", a.mk_int()), m);
    expr_ref cb(m.mk_const("b", a.mk_int()), m);
    sort* integer = a.mk_int();
    sort* sorts[5] = { integer, integer, integer, integer, integer };
    symbol names[5] = { symbol("y"), symbol("q"), symbol("r2"), symbol("q3"), symbol("r") };
    // The last declared variable, r, has index 0.
    expr_ref y(m.mk_var(4, integer), m), q(m.mk_var(3, integer), m), r2(m.mk_var(2, integer), m);
    expr_ref q3(m.mk_var(1, integer), m), r(m.mk_var(0, integer), m);
    expr_ref_vector body(m);
    body.push_back(a.mk_le(a.mk_int(0), y));
    body.push_back(a.mk_le(y, a.mk_int(1)));
    body.push_back(m.mk_eq(a.mk_add(ca, a.mk_int(3)), a.mk_add(a.mk_mul(a.mk_int(6), q), r2)));
    body.push_back(a.mk_le(a.mk_int(0), r2));
    body.push_back(a.mk_lt(r2, a.mk_int(6)));
    body.push_back(m.mk_eq(a.mk_add(q, a.mk_mul(a.mk_int(2), ca)), a.mk_add(a.mk_mul(a.mk_int(3), q3), r)));
    body.push_back(a.mk_le(a.mk_int(0), r));
    body.push_back(a.mk_lt(r, a.mk_int(3)));
    body.push_back(a.mk_le(a.mk_add(r, a.mk_mul(a.mk_int(3), cb)), a.mk_int(5)));
    ctx.add_hard_constraint(m.mk_exists(5, sorts, names, mk_and(body)));
    for (expr* v : { ca.get(), cb.get() }) {
        ctx.add_hard_constraint(a.mk_ge(v, a.mk_int(-4)));
        ctx.add_hard_constraint(a.mk_le(v, a.mk_int(4)));
    }
    expr_ref sum(a.mk_add(ca, cb), m);
    ctx.add_objective(to_app(sum.get()), false);
    check_optimum(ctx, sum, -8);
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
    tst_negative_divisor();
    tst_positive_divisor_offset();
    tst_negated_coefficient();
    tst_qe_disagrees();
    tst_nonlinear_kept();
}
