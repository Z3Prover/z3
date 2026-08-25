/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/bool_rewriter.h"
#include "qe/lite/qe_lite_tactic.h"
#include "smt/smt_context.h"

static expr_ref apply_qe_lite(ast_manager& m, expr* fml) {
    expr_ref result(fml, m);
    proof_ref pr(m);
    qe_lite qe(m, params_ref());
    qe(result, pr);
    return result;
}

static void test_disequality_elimination() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    bool_rewriter rw(m);

    sort* s = bv.mk_sort(3);
    expr_ref x(m.mk_var(0, s), m);
    app_ref p(m.mk_fresh_const("p", m.mk_bool_sort()), m);
    expr_ref eq0(m.mk_eq(x, bv.mk_numeral(0, 3)), m);
    expr_ref eq1(m.mk_eq(x, bv.mk_numeral(1, 3)), m);
    expr_ref guarded(m);
    rw.mk_and(eq1, m.mk_not(p), guarded);
    expr* args[] = { p, m.mk_not(eq0), m.mk_not(guarded) };
    expr_ref body(m);
    rw.mk_and(3, args, body);
    symbol name("x");
    expr_ref fml(m.mk_exists(1, &s, &name, body), m);

    fml = apply_qe_lite(m, fml);
    VERIFY(!has_quantifiers(fml));

    smt_params params;
    smt::context ctx(m, params);
    ctx.assert_expr(m.mk_not(m.mk_iff(fml, p)));
    VERIFY(l_false == ctx.check());
}

static void test_fully_forbidden_bv() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    bool_rewriter rw(m);

    sort* s = bv.mk_sort(1);
    expr_ref x(m.mk_var(0, s), m);
    expr* args[] = {
        m.mk_not(m.mk_eq(x, bv.mk_numeral(0, 1))),
        m.mk_not(m.mk_eq(x, bv.mk_numeral(1, 1)))
    };
    expr_ref body(m);
    rw.mk_and(2, args, body);
    symbol name("x");
    expr_ref fml(m.mk_exists(1, &s, &name, body), m);

    fml = apply_qe_lite(m, fml);
    smt_params params;
    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    VERIFY(l_false == ctx.check());
}

static void test_mixed_sort_declarations() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);
    bv_util bv(m);
    bool_rewriter rw(m);

    sort* sorts[] = { arith.mk_int(), bv.mk_sort(1) };
    symbol names[] = { symbol("x"), symbol("y") };
    expr_ref x(m.mk_var(1, sorts[0]), m);
    expr_ref y(m.mk_var(0, sorts[1]), m);
    expr* args[] = {
        arith.mk_gt(x, arith.mk_int(3)),
        m.mk_not(m.mk_eq(y, bv.mk_numeral(0, 1))),
        m.mk_not(m.mk_eq(y, bv.mk_numeral(1, 1)))
    };
    expr_ref body(m);
    rw.mk_and(3, args, body);
    expr_ref fml(m.mk_exists(2, sorts, names, body), m);

    fml = apply_qe_lite(m, fml);
    smt_params params;
    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    VERIFY(l_false == ctx.check());
}

static void test_lambda_unchanged() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    sort* s = arith.mk_int();
    symbol name("x");
    expr_ref x(m.mk_var(0, s), m);
    expr_ref body(m.mk_not(m.mk_eq(x, arith.mk_int(0))), m);
    expr_ref fml(m.mk_lambda(1, &s, &name, body), m);
    expr_ref result = apply_qe_lite(m, fml);

    smt_params params;
    smt::context ctx(m, params);
    ctx.assert_expr(m.mk_not(m.mk_eq(fml, result)));
    VERIFY(l_false == ctx.check());
}

void tst_qe_lite() {
    test_disequality_elimination();
    test_fully_forbidden_bv();
    test_mixed_sort_declarations();
    test_lambda_unchanged();
}
