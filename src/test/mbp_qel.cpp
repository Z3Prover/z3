
/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    mbp_qel.cpp

Abstract:

    Unit tests for model-based projection with QEL (term-graph based)

Author:

    Hari Govind V K (hgvk94) 2025-05-25

--*/

#include "qe/qe_mbp.h"
#include "qe/mbp/mbp_qel_util.h"
#include "qe/qsat.h"
#include "ast/reg_decl_plugins.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "smt/smt_context.h"
#include "params/smt_params.h"
#include <iostream>

// Test that MBP with QEL does not return false for a satisfiable formula
// involving datatype accessors applied past the end of a list.
//
// Formula: (and ((_ is cons) x) ((_ is nil) (tl x)) (= nil (tl (tl x))) (< 8 n))
// Project: x
// Expected: result should imply n >= 9 (and model should satisfy it)
// Bug: QEL was returning false because rm_accessor unconditionally
//      assumed (tl x) has constructor cons when eliminating (tl (tl x)),
//      contradicting the ((_ is nil) (tl x)) literal.
static void test_dt_accessor_past_end() {
    std::cout << "test_dt_accessor_past_end\n";
    ast_manager m;
    reg_decl_plugins(m);
    datatype_util dt(m);
    arith_util a(m);

    // Create list datatype: (declare-datatypes ((L 0)) (((cons (hd Int) (tl L)) (nil))))
    sort_ref int_sort(a.mk_int(), m);
    func_decl_ref cons(m), is_cons(m), head(m), tail(m), nil(m), is_nil(m);
    sort_ref L = dt.mk_list_datatype(int_sort, symbol("L"),
                                     cons, is_cons, head, tail, nil, is_nil);

    // Declare variables
    app_ref x(m.mk_const("x", L), m);
    app_ref n(m.mk_const("n", int_sort), m);

    // Build formula: (and ((_ is cons) x) ((_ is nil) (tl x)) (= nil (tl (tl x))) (< 8 n))
    expr_ref tl_x(m.mk_app(tail, x.get()), m);
    expr_ref tl_tl_x(m.mk_app(tail, tl_x.get()), m);
    expr_ref nil_val(m.mk_const(nil), m);

    expr_ref is_cons_x(m.mk_app(is_cons, x.get()), m);
    expr_ref is_nil_tl_x(m.mk_app(is_nil, tl_x.get()), m);
    expr_ref eq_nil_tl_tl_x(m.mk_eq(nil_val, tl_tl_x), m);
    expr_ref lt_8_n(a.mk_lt(a.mk_int(8), n), m);

    expr_ref_vector conjs(m);
    conjs.push_back(is_cons_x).push_back(is_nil_tl_x).push_back(eq_nil_tl_tl_x).push_back(lt_8_n);
    expr_ref fml(m.mk_and(conjs), m);

    std::cout << "  formula:\n     " << mk_pp(fml, m, 5) << "\n";

    // Get a model
    smt_params params;
    params.m_model = true;
    model_ref mdl;
    {
        smt::context ctx(m, params);
        ctx.assert_expr(fml);
        lbool result = ctx.check();
        VERIFY(result == l_true);
        ctx.get_model(mdl);
    }

    std::cout << "  model: x = " << mk_pp((*mdl)(x), m)
              << ", n = " << mk_pp((*mdl)(n), m) << "\n";

    // Call MBP with QEL enabled
    app_ref_vector vars(m);
    vars.push_back(x);

    params_ref p;
    p.set_bool("qsat_use_qel", true);
    qe::mbproj mbp(m, p);
    expr_ref projected(fml, m);
    mbp.spacer(vars, *mdl.get(), projected);

    std::cout << "  projected (qel=true):\n     " << mk_pp(projected, m, 5) << "\n";

    // The result must not be false
    VERIFY(!m.is_false(projected));

    // The model should satisfy the projected formula
    VERIFY(mdl->is_true(projected));

    // x should have been eliminated
    VERIFY(vars.empty());

    std::cout << "  PASS\n\n";
}

// Same test but with a deeper list structure:
// x is a 2-element list with a past-end accessor constraint
// Formula: (and ((_ is cons) x) ((_ is cons) (tl x)) ((_ is nil) (tl (tl x)))
//               (= nil (tl (tl (tl x)))) (< 8 n))
static void test_dt_accessor_past_end_depth2() {
    std::cout << "test_dt_accessor_past_end_depth2\n";
    ast_manager m;
    reg_decl_plugins(m);
    datatype_util dt(m);
    arith_util a(m);

    sort_ref int_sort(a.mk_int(), m);
    func_decl_ref cons(m), is_cons(m), head(m), tail(m), nil(m), is_nil(m);
    sort_ref L = dt.mk_list_datatype(int_sort, symbol("L"),
                                     cons, is_cons, head, tail, nil, is_nil);

    app_ref x(m.mk_const("x", L), m);
    app_ref n(m.mk_const("n", int_sort), m);

    // Build: (and (is-cons x) (is-cons (tl x)) (is-nil (tl (tl x)))
    //             (= nil (tl (tl (tl x)))) (< 8 n))
    expr_ref tl_x(m.mk_app(tail, x.get()), m);
    expr_ref tl_tl_x(m.mk_app(tail, tl_x.get()), m);
    expr_ref tl_tl_tl_x(m.mk_app(tail, tl_tl_x.get()), m);
    expr_ref nil_val(m.mk_const(nil), m);

    expr_ref is_cons_x(m.mk_app(is_cons, x.get()), m);
    expr_ref is_cons_tl_x(m.mk_app(is_cons, tl_x.get()), m);
    expr_ref is_nil_tl_tl_x(m.mk_app(is_nil, tl_tl_x.get()), m);
    expr_ref eq_nil_tl3(m.mk_eq(nil_val, tl_tl_tl_x), m);
    expr_ref lt_8_n(a.mk_lt(a.mk_int(8), n), m);

    expr_ref_vector conjs(m);
    conjs.push_back(is_cons_x).push_back(is_cons_tl_x).push_back(is_nil_tl_tl_x).push_back(eq_nil_tl3).push_back(lt_8_n);
    expr_ref fml(m.mk_and(conjs), m);

    std::cout << "  formula:\n     " << mk_pp(fml, m, 5) << "\n";

    smt_params sparams;
    sparams.m_model = true;
    model_ref mdl;
    {
        smt::context ctx(m, sparams);
        ctx.assert_expr(fml);
        lbool result = ctx.check();
        VERIFY(result == l_true);
        ctx.get_model(mdl);
    }

    std::cout << "  model: x = " << mk_pp((*mdl)(x), m)
              << ", n = " << mk_pp((*mdl)(n), m) << "\n";

    app_ref_vector vars(m);
    vars.push_back(x);

    params_ref p;
    p.set_bool("qsat_use_qel", true);
    qe::mbproj mbp(m, p);
    expr_ref projected(fml, m);
    mbp.spacer(vars, *mdl.get(), projected);

    std::cout << "  projected (qel=true):\n     " << mk_pp(projected, m, 5) << "\n";

    VERIFY(!m.is_false(projected));
    VERIFY(mdl->is_true(projected));
    VERIFY(vars.empty());

    std::cout << "  PASS\n\n";
}

// Test with multiple DT variables projected simultaneously
// Formula: (and (= nil (tl (tl (tl x)))) ((_ is nil) (tl (tl x)))
//               ((_ is cons) y) ((_ is nil) (tl y)) (< 8 n))
// Project: x, y
static void test_dt_multiple_vars() {
    std::cout << "test_dt_multiple_vars\n";
    ast_manager m;
    reg_decl_plugins(m);
    datatype_util dt(m);
    arith_util a(m);

    sort_ref int_sort(a.mk_int(), m);
    func_decl_ref cons(m), is_cons(m), head(m), tail(m), nil(m), is_nil(m);
    sort_ref L = dt.mk_list_datatype(int_sort, symbol("L"),
                                     cons, is_cons, head, tail, nil, is_nil);

    app_ref x(m.mk_const("x", L), m);
    app_ref y(m.mk_const("y", L), m);
    app_ref n(m.mk_const("n", int_sort), m);

    expr_ref tl_x(m.mk_app(tail, x.get()), m);
    expr_ref tl_tl_x(m.mk_app(tail, tl_x.get()), m);
    expr_ref tl_tl_tl_x(m.mk_app(tail, tl_tl_x.get()), m);
    expr_ref tl_y(m.mk_app(tail, y.get()), m);
    expr_ref nil_val(m.mk_const(nil), m);

    expr_ref eq_nil_tl3x(m.mk_eq(nil_val, tl_tl_tl_x), m);
    expr_ref is_nil_tl2x(m.mk_app(is_nil, tl_tl_x.get()), m);
    expr_ref is_cons_y(m.mk_app(is_cons, y.get()), m);
    expr_ref is_nil_tl_y(m.mk_app(is_nil, tl_y.get()), m);
    expr_ref lt_8_n(a.mk_lt(a.mk_int(8), n), m);

    expr_ref_vector conjs(m);
    conjs.push_back(eq_nil_tl3x).push_back(is_nil_tl2x).push_back(is_cons_y).push_back(is_nil_tl_y).push_back(lt_8_n);
    expr_ref fml(m.mk_and(conjs), m);

    std::cout << "  formula:\n     " << mk_pp(fml, m, 5) << "\n";

    smt_params sparams;
    sparams.m_model = true;
    model_ref mdl;
    {
        smt::context ctx(m, sparams);
        ctx.assert_expr(fml);
        lbool result = ctx.check();
        VERIFY(result == l_true);
        ctx.get_model(mdl);
    }

    app_ref_vector vars(m);
    vars.push_back(x);
    vars.push_back(y);

    params_ref p;
    p.set_bool("qsat_use_qel", true);
    qe::mbproj mbp(m, p);
    expr_ref projected(fml, m);
    mbp.spacer(vars, *mdl.get(), projected);

    std::cout << "  projected (qel=true):\n     " << mk_pp(projected, m, 5) << "\n";

    VERIFY(!m.is_false(projected));
    VERIFY(mdl->is_true(projected));
    VERIFY(vars.empty());

    std::cout << "  PASS\n\n";
}

static void test_qe2_does_not_expose_fresh_constant() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);

    sort_ref bool_sort(m.mk_bool_sort(), m);
    app_ref x(m.mk_const("x", bool_sort), m);
    app_ref x2(m.mk_const("x2", bool_sort), m);
    expr_ref bound_var(m.mk_var(0, bool_sort), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref condition(m.mk_or(x, bound_var), m);
    expr_ref ite(m.mk_ite(condition, zero, one), m);
    expr* distinct_args[] = { zero, ite };
    expr_ref body(m.mk_or(x2, m.mk_distinct(2, distinct_args)), m);
    sort* sorts[] = { bool_sort };
    symbol names[] = { symbol("X") };
    expr_ref quantified(m.mk_forall(1, sorts, names, body), m);

    goal_ref input = alloc(goal, m);
    input->assert_expr(quantified);
    tactic_ref qe2 = mk_qe2_tactic(m);
    goal_ref_buffer result;
    (*qe2)(input, result);

    VERIFY(result.size() == 1);
    expr_ref_vector formulas(m);
    result[0]->get_formulas(formulas);
    expr_ref projected(m.mk_and(formulas), m);
    VERIFY(!has_quantifiers(projected));

    obj_hashtable<app> constants;
    collect_uninterp_consts(projected, constants);
    for (app* constant : constants)
        VERIFY(constant == x || constant == x2);

    // X = true reduces the body to x2, while x2 = true satisfies every X.
    smt_params sparams;
    smt::context ctx(m, sparams);
    ctx.assert_expr(m.mk_not(m.mk_eq(projected, x2)));
    VERIFY(ctx.check() == l_false);
}

void tst_mbp_qel() {
    test_dt_accessor_past_end();
    test_dt_accessor_past_end_depth2();
    test_dt_multiple_vars();
    test_qe2_does_not_expose_fresh_constant();
}
