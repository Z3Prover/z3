
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "api/z3.h"
#include "api/z3_private.h"
#include <algorithm>
#include <cstring>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>
#include "util/util.h"
#include "util/trace.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/for_each_expr.h"
#include "ast/proofs/proof_checker.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/simplifiers/demodulator_simplifier.h"
#include "ast/simplifiers/bit2int.h"
#include "ast/simplifiers/recfun_finder.h"
#include "ast/simplifiers/seq_regular_simplifier.h"
#include "ast/occurs.h"
#include "ast/simplifiers/solve_eqs.h"
#include "ast/simplifiers/pull_nested_quantifiers.h"
#include "ast/simplifiers/lambda_simplifier.h"
#include "ast/simplifiers/randomizer.h"
#include "ast/simplifiers/rewriter_simplifier.h"
#include "ast/simplifiers/then_simplifier.h"
#include "ast/array_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_solver.h"
#include "smt/smt_context.h"
#include "solver/solver.h"
#include "solver/simplifier_solver.h"
#include "solver/assertions/asserted_formulas.h"
#include "qe/qe_tactic.h"
#include "tactic/tactical.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/dependent_expr_state_tactic.h"


static void ev_const(Z3_context ctx, Z3_ast e) {
    Z3_ast r = Z3_simplify(ctx, e);
    TRACE(simplifier, 
          tout << Z3_ast_to_string(ctx, e) << " -> ";
          tout << Z3_ast_to_string(ctx, r) << "\n";);
    Z3_ast_kind k = Z3_get_ast_kind(ctx, r);
    ENSURE(k == Z3_NUMERAL_AST ||
            (k == Z3_APP_AST && 
             (Z3_OP_TRUE  == Z3_get_decl_kind(ctx,Z3_get_app_decl(ctx, Z3_to_app(ctx, r))) ||
              Z3_OP_FALSE == Z3_get_decl_kind(ctx,Z3_get_app_decl(ctx, Z3_to_app(ctx, r))))));
}

static void expect_simplifies_to(Z3_context ctx, Z3_ast input, Z3_ast expected) {
    Z3_ast actual = Z3_simplify(ctx, input);
    expected = Z3_simplify(ctx, expected);
    TRACE(simplifier,
        tout << Z3_ast_to_string(ctx, input) << " -> "
             << Z3_ast_to_string(ctx, actual) << "\n";);
    ENSURE(Z3_is_eq_ast(ctx, actual, expected));
}

static void expect_context_simplifies_to(
    Z3_context ctx, Z3_ast context, Z3_ast input, Z3_ast expected) {
    Z3_goal goal = Z3_mk_goal(ctx, false, false, false);
    Z3_goal_inc_ref(ctx, goal);
    Z3_goal_assert(ctx, goal, context);
    Z3_goal_assert(ctx, goal, input);

    Z3_tactic tactic = Z3_mk_tactic(ctx, "propagate-bv-bounds2");
    Z3_tactic_inc_ref(ctx, tactic);
    Z3_apply_result result = Z3_tactic_apply(ctx, tactic, goal);
    Z3_apply_result_inc_ref(ctx, result);
    ENSURE(Z3_apply_result_get_num_subgoals(ctx, result) == 1);

    expected = Z3_simplify(ctx, expected);
    Z3_goal subgoal = Z3_apply_result_get_subgoal(ctx, result, 0);
    bool found = false;
    for (unsigned i = 0; i < Z3_goal_size(ctx, subgoal); ++i)
        found |= Z3_is_eq_ast(ctx, Z3_goal_formula(ctx, subgoal, i), expected);
    ENSURE(found);

    Z3_apply_result_dec_ref(ctx, result);
    Z3_tactic_dec_ref(ctx, tactic);
    Z3_goal_dec_ref(ctx, goal);
}

static void test_bv() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv1 = Z3_mk_bv_sort(ctx,1);
    Z3_sort bv2 = Z3_mk_bv_sort(ctx,2);
    Z3_sort bv72 = Z3_mk_bv_sort(ctx,72);
    Z3_ast bit1_1 = Z3_mk_numeral(ctx, "1", bv1);
    Z3_ast bit3_2 = Z3_mk_numeral(ctx, "3", bv2);

    Z3_ast e = Z3_mk_eq(ctx, bit3_2, Z3_mk_sign_ext(ctx, 1, bit1_1));
    ENSURE(Z3_simplify(ctx, e) == Z3_mk_true(ctx));
    TRACE(simplifier, tout << Z3_ast_to_string(ctx, e) << "\n";);

    Z3_ast b12 = Z3_mk_numeral(ctx, "12", bv72);
    Z3_ast b13 = Z3_mk_numeral(ctx, "13", bv72);

    ev_const(ctx, Z3_mk_bvnot(ctx,b12));
    ev_const(ctx, Z3_mk_bvnot(ctx,Z3_simplify(ctx, Z3_mk_bvnot(ctx, b12))));
    ev_const(ctx, Z3_mk_bvand(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvxor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvnand(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvnor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvxnor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvneg(ctx,b12));
    ev_const(ctx, Z3_mk_bvadd(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsub(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvmul(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvudiv(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsdiv(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsrem(ctx,b12,b13));

    ev_const(ctx, Z3_mk_bvuge(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsge(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvugt(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsgt(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvule(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvult(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsle(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvslt(ctx,b12,b13));

    ev_const(ctx, Z3_mk_concat(ctx,b12,b13));
    ev_const(ctx, Z3_mk_extract(ctx,43,1,b13));
    ev_const(ctx, Z3_mk_sign_ext(ctx,33,b13));
    ev_const(ctx, Z3_mk_zero_ext(ctx,33,b13));
    ev_const(ctx, Z3_mk_bvshl(ctx,b12,b13));

    ev_const(ctx, Z3_mk_bvshl(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvlshr(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvashr(ctx,b12,b13));

    ev_const(ctx, Z3_mk_rotate_left(ctx,21,b13));
    ev_const(ctx, Z3_mk_rotate_right(ctx,21,b13));

    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_sort bv16 = Z3_mk_bv_sort(ctx, 16);
    Z3_ast x8 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x8"), bv8);
    Z3_ast y8 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y8"), bv8);
    Z3_ast x16 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x16"), bv16);
    Z3_ast cond = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "cond"), Z3_mk_bool_sort(ctx));
    Z3_ast zx = Z3_mk_zero_ext(ctx, 8, x8);
    Z3_ast zy = Z3_mk_zero_ext(ctx, 8, y8);
    Z3_ast sx = Z3_mk_sign_ext(ctx, 8, x8);
    Z3_ast sy = Z3_mk_sign_ext(ctx, 8, y8);

    expect_simplifies_to(ctx,
        Z3_mk_extract(ctx, 7, 0, Z3_mk_bvudiv(ctx, zx, zy)),
        Z3_mk_bvudiv(ctx, x8, y8));
    expect_simplifies_to(ctx,
        Z3_mk_extract(ctx, 7, 0, Z3_mk_bvurem(ctx, zx, zy)),
        Z3_mk_bvurem(ctx, x8, y8));
    expect_simplifies_to(ctx,
        Z3_mk_extract(ctx, 7, 0, Z3_mk_bvsdiv(ctx, sx, sy)),
        Z3_mk_bvsdiv(ctx, x8, y8));
    expect_simplifies_to(ctx,
        Z3_mk_extract(ctx, 7, 0, Z3_mk_bvsrem(ctx, sx, sy)),
        Z3_mk_bvsrem(ctx, x8, y8));
    expect_simplifies_to(ctx,
        Z3_mk_bvsle(ctx, zx, zy),
        Z3_mk_bvule(ctx, x8, y8));
    expect_simplifies_to(ctx,
        Z3_mk_bvand(ctx, zx, zy),
        Z3_mk_zero_ext(ctx, 8, Z3_mk_bvand(ctx, x8, y8)));
    expect_simplifies_to(ctx,
        Z3_mk_bvor(ctx, zx, zy),
        Z3_mk_zero_ext(ctx, 8, Z3_mk_bvor(ctx, x8, y8)));
    expect_simplifies_to(ctx,
        Z3_mk_ite(ctx, cond, zx, zy),
        Z3_mk_zero_ext(ctx, 8, Z3_mk_ite(ctx, cond, x8, y8)));
    expect_simplifies_to(ctx,
        Z3_mk_ite(ctx, cond, sx, sy),
        Z3_mk_sign_ext(ctx, 8, Z3_mk_ite(ctx, cond, x8, y8)));

    Z3_ast bv12 = Z3_mk_numeral(ctx, "12", bv16);
    Z3_ast bv4 = Z3_mk_numeral(ctx, "4", bv16);
    expect_simplifies_to(ctx,
        Z3_mk_bvsrem(ctx, Z3_mk_bvsrem(ctx, x16, bv12), bv4),
        Z3_mk_bvsrem(ctx, x16, bv4));

    Z3_ast y16 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y16"), bv16);
    Z3_ast bv255 = Z3_mk_numeral(ctx, "255", bv16);
    expect_context_simplifies_to(ctx,
        Z3_mk_bvule(ctx, y16, bv255),
        Z3_mk_eq(ctx, zx, y16),
        Z3_mk_eq(ctx, x8, Z3_mk_extract(ctx, 7, 0, y16)));

    Z3_ast bv0 = Z3_mk_numeral(ctx, "0", bv8);
    Z3_sort bv9 = Z3_mk_bv_sort(ctx, 9);
    Z3_ast bv0_9 = Z3_mk_numeral(ctx, "0", bv9);
    Z3_ast nonnegative_x = Z3_mk_concat(ctx, bv0_9, Z3_mk_extract(ctx, 6, 0, x8));
    expect_context_simplifies_to(ctx,
        Z3_mk_bvsle(ctx, bv0, x8),
        Z3_mk_eq(ctx, x16, sx),
        Z3_mk_eq(ctx, x16, nonnegative_x));

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

static void test_datatypes() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort int_ty, int_list;
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;
    Z3_ast nil, l1;    

    int_ty = Z3_mk_int_sort(ctx);

    int_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "int_list"), int_ty,
                               &nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);
                    
    (void) int_list;
    nil = Z3_mk_app(ctx, nil_decl, 0, nullptr);

    Z3_ast a = Z3_simplify(ctx, Z3_mk_app(ctx, is_nil_decl, 1, &nil));
    ENSURE(a == Z3_mk_true(ctx));

    a = Z3_simplify(ctx, Z3_mk_app(ctx, is_cons_decl, 1, &nil));
    ENSURE(a == Z3_mk_false(ctx));

    Z3_ast one = Z3_mk_numeral(ctx, "1", int_ty);
    Z3_ast args[2] = { one, nil };
    l1 = Z3_mk_app(ctx, cons_decl, 2, args);
    ENSURE(nil == Z3_simplify(ctx, Z3_mk_app(ctx, tail_decl, 1, &l1))); 
    ENSURE(one == Z3_simplify(ctx, Z3_mk_app(ctx, head_decl, 1, &l1))); 

    ENSURE(Z3_mk_false(ctx) == Z3_simplify(ctx, Z3_mk_eq(ctx, nil, l1)));
    
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}


static void test_skolemize_bug() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort Real = Z3_mk_real_sort(ctx);
    Z3_ast x = Z3_mk_bound(ctx, 0, Real);
    Z3_symbol x_name = Z3_mk_string_symbol(ctx, "x");
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), Real);
    Z3_ast xp = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "xp"), Real);
    Z3_ast n0 = Z3_mk_numeral(ctx, "0", Real);
    Z3_ast n1 = Z3_mk_numeral(ctx, "1", Real);
    Z3_ast args1[2] = { x, n1 };
    Z3_ast args2[2] = { x, y };
    Z3_ast args[2] = { Z3_mk_eq(ctx, Z3_mk_add(ctx, 2, args1), xp), 
                       Z3_mk_ge(ctx, Z3_mk_add(ctx, 2, args2), n0) };
    Z3_ast f  = Z3_mk_and(ctx, 2, args);
    Z3_ast f2 = Z3_mk_exists(ctx, 0, 0, nullptr, 1, &Real, &x_name, f);
    std::cout << Z3_ast_to_string(ctx, f2) << "\n";
    Z3_ast f3 = Z3_simplify(ctx, f2);
    std::cout << Z3_ast_to_string(ctx, f3) << "\n";

    Z3_del_context(ctx);
}


static void test_bool() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast a = Z3_simplify(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, Z3_mk_false(ctx), Z3_mk_true(ctx))));
    Z3_ast b = Z3_simplify(ctx, Z3_mk_not(ctx, Z3_mk_iff(ctx, Z3_mk_false(ctx), Z3_mk_true(ctx))));
    ENSURE(Z3_mk_true(ctx) == a);
    ENSURE(Z3_mk_true(ctx) == b);
    TRACE(simplifier, tout << Z3_ast_to_string(ctx, a) << "\n";);
    TRACE(simplifier, tout << Z3_ast_to_string(ctx, b) << "\n";);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

static void test_fpa() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort fp64 = Z3_mk_fpa_sort(ctx, 11, 53);
    // x is created before y, so ast_lt orders x before y and fp.add RNE y x should normalize to fp.add RNE x y.
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), fp64);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), fp64);
    Z3_ast rm = Z3_mk_fpa_rne(ctx);
    Z3_ast add_yx = Z3_mk_fpa_add(ctx, rm, y, x);
    Z3_ast add_xy = Z3_mk_fpa_add(ctx, rm, x, y);
    Z3_ast simp = Z3_simplify(ctx, add_yx);
    ENSURE(Z3_is_eq_ast(ctx, simp, add_xy));
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

static void test_const_array_lambda() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* cases[] = {
        "(assert (forall ((a Int))"
        " (= ((as const (Array Int Int)) a) (lambda ((x Int)) x))))"
        "(assert (forall ((a Int) (x Int)) (= x a)))",

        "(assert (forall ((a Int))"
        " (= (lambda ((x Int)) x) ((as const (Array Int Int)) a))))"
        "(assert (forall ((a Int) (x Int)) (= x a)))",

        "(assert (forall ((a Int) (b (Array Int Int)))"
        " (= ((as const (Array Int Int)) a) (lambda ((x Int)) x))))"
        "(assert (forall ((a Int) (b (Array Int Int)) (x Int)) (= x a)))",

        "(assert (forall ((a Int))"
        " (= ((as const (Array Int Int Int)) a) (lambda ((x Int) (y Int)) (+ x y)))))"
        "(assert (forall ((a Int) (x Int) (y Int)) (= (+ x y) a)))",

        "(assert (forall ((a Int))"
        " (= ((as const (Array Int Int)) (+ a 1)) (lambda ((x Int)) (+ a x)))))"
        "(assert (forall ((a Int) (x Int)) (= (+ a x) (+ a 1))))",

        "(declare-const a Int)"
        "(assert (= ((as const (Array Int Int)) a) (lambda ((x Int)) x)))"
        "(assert (forall ((x Int)) (! (= x a) :skolemid generated)))"
    };

    for (char const* test : cases) {
        Z3_ast_vector fmls = Z3_parse_smtlib2_string(ctx, test, 0, nullptr, nullptr, 0, nullptr, nullptr);
        Z3_ast_vector_inc_ref(ctx, fmls);
        ENSURE(Z3_ast_vector_size(ctx, fmls) == 2);
        Z3_ast input = Z3_ast_vector_get(ctx, fmls, 0);
        Z3_ast expected = Z3_ast_vector_get(ctx, fmls, 1);
        Z3_ast actual = Z3_simplify(ctx, input);
        ENSURE(Z3_is_well_sorted(ctx, actual));
        expect_simplifies_to(ctx, input, expected);

        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        Z3_solver_assert(ctx, solver, input);
        ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
        Z3_solver_dec_ref(ctx, solver);
        Z3_ast_vector_dec_ref(ctx, fmls);
    }
    Z3_del_context(ctx);
}

static void test_array() {
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort i = Z3_mk_int_sort(ctx);
    Z3_ast n1 = Z3_mk_numeral(ctx, "1", i);
    Z3_ast n2 = Z3_mk_numeral(ctx, "2", i);
    Z3_ast n3 = Z3_mk_numeral(ctx, "3", i);
    Z3_ast n4 = Z3_mk_numeral(ctx, "4", i);
    Z3_ast s1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"s1"), i);
    Z3_ast s2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"s2"), i);
    (void) s2;
    
    Z3_ast c1 = Z3_mk_const_array(ctx, i, n1);
    Z3_ast x1  = Z3_mk_store(ctx, Z3_mk_store(ctx, c1, n2, n3), n1, n4);
    Z3_ast x2  = Z3_mk_store(ctx, Z3_mk_store(ctx, c1, n1, n4), n2, n3);
    Z3_ast x3  = Z3_mk_store(ctx, Z3_mk_store(ctx, c1, s1, n1), n2, n3);
    Z3_ast x4  = Z3_mk_store(ctx, Z3_mk_store(ctx, Z3_mk_store(ctx, c1, n2, n3), n1, n4), n2, n3);
    Z3_ast xs[4] = { x1, x2, x3, x4};
    Z3_ast exy  = Z3_mk_eq(ctx, x2, x1);
    Z3_ast rxy  = Z3_simplify(ctx, exy);
    (void)rxy;

    TRACE(simplifier, tout << Z3_ast_to_string(ctx, rxy) << "\n";);
    TRACE(simplifier, tout << Z3_ast_to_string(ctx, Z3_simplify(ctx, Z3_mk_eq(ctx, x2, x3))) << "\n";);
    // ENSURE(rxy == Z3_mk_true(ctx));
    // ENSURE(Z3_simplify(ctx, Z3_mk_eq(ctx, x2, x3)) == Z3_mk_false(ctx));
    
    for (unsigned i = 0; i < 4; ++i) {
        for (unsigned j = 0; j < 4; ++j) {
            exy  = Z3_mk_eq(ctx, xs[i], xs[j]);
            rxy  = Z3_simplify(ctx, exy);
            
            TRACE(simplifier, 
                  tout << Z3_ast_to_string(ctx, exy);
                  tout << " -> " << Z3_ast_to_string(ctx, rxy) << "\n";  
                  );
        }
    }

    Z3_ast sel1 = Z3_mk_select(ctx, x1, n1);
    Z3_ast sel2 = Z3_mk_select(ctx, x1, n4);
    (void)sel1;
    (void)sel2;

    TRACE(simplifier, 
          tout << Z3_ast_to_string(ctx,  Z3_simplify(ctx, sel1)) << "\n";
          tout << Z3_ast_to_string(ctx,  Z3_simplify(ctx, sel2)) << "\n";
          );

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

static void test_recfun_finder() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    sort* int_sort = a.mk_int();
    sort* domain[1] = { int_sort };
    func_decl_ref f(m.mk_func_decl(symbol("f"), 1, domain, int_sort), m);
    var_ref x(m.mk_var(0, int_sort), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref fx(m.mk_app(f, x.get()), m);
    expr_ref xm1(a.mk_sub(x, one), m);
    expr_ref rec(m.mk_app(f, xm1.get()), m);
    expr_ref condition(m.mk_eq(x, zero), m);
    expr_ref else_value(a.mk_add(one, rec), m);
    expr_ref body(m.mk_ite(condition, zero, else_value), m);
    expr_ref eq(m.mk_eq(fx, body), m);
    symbol x_name("x");
    quantifier_ref q(m.mk_forall(1, &int_sort, &x_name, eq), m);

    base_dependent_expr_state st(m);
    st.push();
    st.add(dependent_expr(m, q, nullptr, nullptr));
    expr_ref three(a.mk_int(3), m);
    expr_ref f3(m.mk_app(f, three.get()), m);
    st.add(dependent_expr(m, m.mk_not(m.mk_eq(f3, three)), nullptr, nullptr));

    recfun_finder rf(m, params_ref(), st);
    rf.push();
    rf.reduce();
    st.flatten_suffix();

    ENSURE(st.qtail() == 1);
    ENSURE(!is_quantifier(st[0].fml()));
    recfun::util ru(m);
    ENSURE(ru.has_defs());
    st.pop(1);
    ENSURE(!ru.has_defs());
}

// A definition whose recursive call already sits under an ite with a
// recursion-free test is registered as is: the sibling conjunct p(x) of the
// recursive call stays in the body of the case instead of becoming a case guard.
static void test_recfun_finder_guarded_body() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    sort* int_sort = a.mk_int();
    sort* domain[1] = { int_sort };
    func_decl_ref f(m.mk_func_decl(symbol("f"), 1, domain, m.mk_bool_sort()), m);
    func_decl_ref p(m.mk_func_decl(symbol("p"), 1, domain, m.mk_bool_sort()), m);
    var_ref x(m.mk_var(0, int_sort), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref fx(m.mk_app(f, x.get()), m);
    expr_ref px(m.mk_app(p, x.get()), m);
    expr_ref xm1(a.mk_sub(x, one), m);
    expr_ref rec(m.mk_app(f, xm1.get()), m);
    expr_ref condition(m.mk_eq(x, zero), m);
    expr_ref else_value(m.mk_and(rec, px), m);
    expr_ref body(m.mk_ite(condition, m.mk_true(), else_value), m);
    expr_ref eq(m.mk_eq(fx, body), m);
    symbol x_name("x");
    quantifier_ref q(m.mk_forall(1, &int_sort, &x_name, eq), m);
    base_dependent_expr_state st(m);
    st.push();
    st.add(dependent_expr(m, q, nullptr, nullptr));
    expr_ref three(a.mk_int(3), m);
    expr_ref f3(m.mk_app(f, three.get()), m);
    st.add(dependent_expr(m, f3, nullptr, nullptr));
    recfun_finder rf(m, params_ref(), st);
    rf.push();
    rf.reduce();
    st.flatten_suffix();
    recfun::util ru(m);
    ENSURE(ru.has_defs());
    recfun::def* d = nullptr;
    for (func_decl* g : ru.get_rec_funs())
        if (g->get_name() == symbol("f"))
            d = &ru.get_def(g);
    ENSURE(d);
    ENSURE(d->get_cases().size() == 2);
    for (recfun::case_def const& c : d->get_cases())
        for (expr* g : c.get_guards())
            ENSURE(!occurs(p, g));
    st.pop(1);
    rf.pop(1);
}

static void test_incremental_demodulator() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    sort* int_sort = a.mk_int();
    sort* domain[1] = { int_sort };
    func_decl_ref f(m.mk_func_decl(symbol("f"), 1, domain, int_sort), m);
    var_ref x(m.mk_var(0, int_sort), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref fx(m.mk_app(f, x.get()), m);
    expr_ref rhs(a.mk_add(x, one), m);
    expr_ref eq(m.mk_eq(fx, rhs), m);
    symbol x_name("x");
    quantifier_ref q(m.mk_forall(1, &int_sort, &x_name, eq), m);

    base_dependent_expr_state st(m);
    demodulator_simplifier demod(m, params_ref(), st);
    st.add(dependent_expr(m, q, nullptr, nullptr));
    demod.reduce();
    st.advance_qhead();

    expr_ref two(a.mk_int(2), m);
    expr_ref three(a.mk_int(3), m);
    expr_ref f2(m.mk_app(f, two.get()), m);
    st.add(dependent_expr(m, m.mk_not(m.mk_eq(f2, three)), nullptr, nullptr));
    demod.reduce();

    ENSURE(m.is_false(st[1].fml()));
}

static void check_simplifier_proofs(ast_manager& m, base_dependent_expr_state& st,
                                    expr_ref_vector const& assertions) {
    proof_checker checker(m);
    for (unsigned i = 0; i < st.qtail(); ++i) {
        proof* pr = st[i].pr();
        ENSURE(pr && m.get_fact(pr) == st[i].fml());
        expr_ref_vector side_conditions(m);
        ENSURE(checker.check(pr, side_conditions));
        for (expr* condition : side_conditions) {
            expr_ref closed(condition, m);
            expr_free_vars variables(condition);
            if (!variables.empty()) {
                // PR_BIND bodies can contribute conditions with free de Bruijn variables.
                expr_ref_vector values(m);
                for (unsigned j = 0; j < variables.size(); ++j)
                    values.push_back(m.mk_fresh_const("proof-var", variables[j] ? variables[j] : m.mk_bool_sort()));
                var_subst substitute(m, false);
                closed = substitute(condition, values);
            }
            solver_ref check(mk_smt_solver(m, params_ref(), symbol()));
            check->assert_expr(m.mk_not(closed));
            ENSURE(check->check_sat(0, nullptr) == l_false);
        }
        for (expr* e : subterms::all(expr_ref(pr, m))) {
            if (!m.is_asserted(e))
                continue;
            bool found = false;
            for (expr* f : assertions)
                found |= f == m.get_fact(to_app(e));
            ENSURE(found);
        }
    }
}

static void test_proof_mode_simplifier_pipeline() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        arith_util a(m);
        expr_ref x(m.mk_const("pipeline-x", a.mk_int()), m);
        expr_ref zero(a.mk_int(0), m), one(a.mk_int(1), m);
        expr_ref sum(a.mk_add(x, zero), m);
        expr_ref original(m.mk_eq(sum, one), m);
        expr_ref expected(m.mk_eq(x, one), m);
        base_dependent_expr_state st(m);
        proof_ref pr(proofs ? m.mk_asserted(original) : nullptr, m);
        st.add(dependent_expr(m, original, pr, nullptr));
        then_simplifier outer(m, params_ref(), st);
        auto* inner = alloc(then_simplifier, m, params_ref(), st);
        inner->add_simplifier(alloc(randomizer_simplifier, m, params_ref(), st));
        inner->add_simplifier(alloc(rewriter_simplifier, m, params_ref(), st));
        outer.add_simplifier(inner);
        outer.reduce();
        ENSURE(st.qtail() == 1 && st[0].fml() != original);
        ENSURE(occurs(x, st[0].fml()) == proofs);
        if (proofs) {
            ENSURE(st[0].fml() == expected);
            expr_ref_vector assertions(m);
            assertions.push_back(original);
            check_simplifier_proofs(m, st, assertions);
        }

        for (bool nested : {false, true}) {
            simplifier_factory factory = [nested](ast_manager& m, params_ref const& p, dependent_expr_state& s) {
                dependent_expr_simplifier* simp = alloc(randomizer_simplifier, m, p, s);
                if (nested) {
                    auto* seq = alloc(then_simplifier, m, p, s);
                    seq->add_simplifier(simp);
                    simp = seq;
                }
                return simp;
            };
            solver_ref backend(mk_smt_solver(m, params_ref(), symbol()));
            solver_ref solver(mk_simplifier_solver(backend.get(), &factory));
            expr_ref positive(a.mk_gt(x, zero), m), negative(a.mk_lt(x, zero), m);
            solver->assert_expr(positive);
            solver->assert_expr(negative);
            ENSURE(solver->check_sat(0, nullptr) == l_false);
            if (proofs) {
                proof_ref refutation(solver->get_proof(), m);
                ENSURE(refutation && m.is_false(m.get_fact(refutation)));
                base_dependent_expr_state result(m);
                result.add(dependent_expr(m, m.mk_false(), refutation, nullptr));
                expr_ref_vector assertions(m);
                assertions.push_back(positive);
                assertions.push_back(negative);
                check_simplifier_proofs(m, result, assertions);
            }
        }
    }
}

class assertion_test_simplifier : public dependent_expr_simplifier {
    std::function<void(dependent_expr_state&)> m_reduce;
public:
    assertion_test_simplifier(ast_manager& m, dependent_expr_state& state,
                             std::function<void(dependent_expr_state&)> reduce):
        dependent_expr_simplifier(m, state), m_reduce(reduce) {}
    char const* name() const override { return "assertion-test"; }
    void reduce() override { m_reduce(m_fmls); }
};

static void test_asserted_formula_plugins() {
    {
        ast_manager m;
        reg_decl_plugins(m);
        expr_ref atom(m.mk_const("assertion-plugin-p", m.mk_bool_sort()), m);
        expr_ref negated(m.mk_not(atom), m);
        expr_ref original(m.mk_not(negated), m);
        params_ref p;
        p.set_bool("preprocess", false);
        smt_params params(p);
        asserted_formulas formulas(m, params, p);
        unsigned calls = 0;
        formulas.register_simplifier([&](ast_manager& m, params_ref const&, dependent_expr_state& state) {
            return alloc(assertion_test_simplifier, m, state, [&](dependent_expr_state& state) {
                ENSURE(calls++ == 0 && state[0].fml() == original);
                state.update(0, dependent_expr(m, atom, nullptr, nullptr));
            });
        });
        formulas.register_simplifier([&](ast_manager& m, params_ref const&, dependent_expr_state& state) {
            return alloc(assertion_test_simplifier, m, state, [&](dependent_expr_state& state) {
                ENSURE(calls++ == 1 && state[0].fml() == atom);
                state.reset_updated();
            });
        });
        formulas.assert_expr(original);
        formulas.reduce();
        ENSURE(calls == 2 && formulas.get_num_formulas() == 1);
        ENSURE(formulas.get_formula(0) == atom);
    }
    {
        ast_manager m;
        reg_decl_plugins(m);
        expr_ref first(m.mk_const("assertion-plugin-first", m.mk_bool_sort()), m);
        expr_ref second(m.mk_const("assertion-plugin-second", m.mk_bool_sort()), m);
        expr_ref input(m), atom(m);
        params_ref p;
        p.set_bool("preprocess", false);
        smt_params params(p);
        asserted_formulas formulas(m, params, p);
        unsigned calls = 0;
        formulas.register_simplifier([&](ast_manager& m, params_ref const&, dependent_expr_state& state) {
            return alloc(assertion_test_simplifier, m, state, [&](dependent_expr_state& state) {
                ENSURE(calls++ % 2 == 0 && state.qtail() == 1 && state[0].fml() == input);
                state.update(0, dependent_expr(m, atom, nullptr, nullptr));
            });
        });
        formulas.register_simplifier([&](ast_manager& m, params_ref const&, dependent_expr_state& state) {
            return alloc(assertion_test_simplifier, m, state, [&](dependent_expr_state& state) {
                ENSURE(calls++ % 2 == 1 && state[0].fml() == atom);
                state.update(0, dependent_expr(m, input, nullptr, nullptr));
            });
        });
        auto add = [&](expr* a) {
            atom = a;
            expr_ref negated(m.mk_not(atom), m);
            input = m.mk_not(negated);
            formulas.assert_expr(input);
            formulas.reduce();
            ENSURE(formulas.get_formula(formulas.get_num_formulas() - 1) == input);
        };
        add(first);
        formulas.commit();
        formulas.push_scope();
        add(second);
        ENSURE(formulas.get_qhead() == 1 && formulas.get_num_formulas() == 2);
        formulas.pop_scope(1);
        ENSURE(formulas.get_num_formulas() == 1);
        formulas.reset();
        add(second);
        ENSURE(calls == 6);
    }
    for (bool proofs : {false, true}) {
        for (bool quantified : {false, true}) {
            ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
            reg_decl_plugins(m);
            arith_util a(m);
            sort* integer = a.mk_int();
            func_decl_ref f(m.mk_func_decl(symbol("assertion-plugin-f"), integer, integer), m);
            expr_ref x(m);
            if (quantified)
                x = m.mk_var(0, integer);
            else
                x = m.mk_const("assertion-plugin-x", integer);
            expr_ref zero(a.mk_int(0), m), sum(a.mk_add(x, zero), m);
            expr_ref fx(m.mk_app(f, x.get()), m);
            expr_ref original(m.mk_eq(fx, sum), m);
            if (quantified) {
                symbol name("x");
                original = m.mk_forall(1, &integer, &name, original);
            }
            params_ref p;
            p.set_bool("preprocess", false);
            p.set_bool("seq.regular", false);
            p.set_sym("string_solver", symbol("seq"));
            smt_params params(p);
            asserted_formulas formulas(m, params, p);
            unsigned calls = 0;
            formulas.register_simplifier([&](ast_manager& m, params_ref const&, dependent_expr_state& state) {
                return alloc(assertion_test_simplifier, m, state, [&](dependent_expr_state& state) {
                    ++calls;
                    ENSURE(state[0].fml() == original);
                    ENSURE(state.proofs_enabled() == proofs && state.has_quantifiers() == quantified);
                    ENSURE((state[0].pr() != nullptr) == proofs);
                });
            });
            formulas.register_simplifier([](ast_manager& m, params_ref const& p, dependent_expr_state& state) {
                return alloc(rewriter_simplifier, m, p, state);
            });
            formulas.assert_expr(original);
            formulas.reduce();
            ENSURE(calls == 1);
            if (proofs) {
                base_dependent_expr_state result(m);
                for (unsigned i = 0; i < formulas.get_num_formulas(); ++i)
                    result.add(dependent_expr(m, formulas.get_formula(i), formulas.get_formula_proof(i), nullptr));
                expr_ref_vector assertions(m);
                assertions.push_back(original);
                check_simplifier_proofs(m, result, assertions);
            }
        }
    }
}

static void test_bit2int_proofs() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    arith_util a(m);
    bv_util bv(m);
    expr_ref u(m.mk_const("mod-u", bv.mk_sort(3)), m);
    expr_ref v(m.mk_const("mod-v", bv.mk_sort(3)), m);
    expr_ref ui(bv.mk_ubv2int(u), m), vi(bv.mk_ubv2int(v), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref negative(a.mk_uminus(ui), m);
    expr_ref neg_v(a.mk_uminus(vi), m);
    expr_ref difference(a.mk_add(ui, neg_v), m);
    expr_ref three(bv.mk_numeral(3, 3), m);
    expr_ref nonzero(bv.mk_ubv2int(three), m);
    expr_ref_vector dividends(m), divisors(m);
    dividends.push_back(ui);
    dividends.push_back(negative);
    dividends.push_back(difference);
    divisors.push_back(zero);
    divisors.push_back(vi);
    divisors.push_back(nonzero);
    bit2int rewrite(m);
    expr_ref result(m);
    proof_ref pr(m);
    for (expr* dividend : dividends) {
        for (expr* divisor : divisors) {
            expr_ref original(a.mk_mod(dividend, divisor), m);
            rewrite(original, result, pr);
            if (divisor == nonzero) {
                ENSURE(bv.is_ubv2int(result));
            }
            else {
                ENSURE(a.is_mod(result));
            }
            solver_ref check(mk_smt_solver(m, params_ref(), symbol()));
            expr_ref equality(m.mk_eq(original, result), m);
            check->assert_expr(m.mk_not(equality));
            ENSURE(check->check_sat(0, nullptr) == l_false);
            if (pr) {
                ENSURE(m.get_fact(pr) == equality);
                base_dependent_expr_state state(m);
                state.add(dependent_expr(m, equality, pr, nullptr));
                expr_ref_vector assertions(m);
                check_simplifier_proofs(m, state, assertions);
            }
        }
    }

    expr_ref one(a.mk_int(1), m);
    expr_ref converted(m.mk_eq(ui, one), m);
    rewrite(converted, result, pr);
    ENSURE(result != converted && pr);
    expr_ref x(m.mk_const("mod-x", a.mk_int()), m);
    expr_ref unchanged(a.mk_gt(x, zero), m);
    rewrite(unchanged, result, pr);
    ENSURE(result == unchanged && !pr);

    base_dependent_expr_state state(m);
    expr_ref_vector assertions(m);
    assertions.push_back(converted);
    assertions.push_back(unchanged);
    assertions.push_back(a.mk_lt(x, zero));
    for (expr* assertion : assertions)
        state.add(dependent_expr(m, assertion, m.mk_asserted(assertion), nullptr));
    bit2int_simplifier simplify(m, params_ref(), state);
    simplify.reduce();
    check_simplifier_proofs(m, state, assertions);
}

static void test_bit2int_zero_divisor_qe() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        arith_util a(m);
        bv_util bv(m);
        expr_ref u(m.mk_const("qe-u", bv.mk_sort(4)), m);
        expr_ref v(m.mk_const("qe-v", bv.mk_sort(4)), m);
        expr_ref ui(bv.mk_ubv2int(u), m), vi(bv.mk_ubv2int(v), m);
        sort* integer = a.mk_int();
        symbol name("x");
        expr_ref x(m.mk_var(0, integer), m);
        expr_ref mod(a.mk_mod(ui, vi), m);
        expr_ref one(bv.mk_numeral(1, 4), m), zero(bv.mk_numeral(0, 4), m);
        expr_ref u_value(m.mk_eq(u, one), m), v_value(m.mk_eq(v, zero), m);
        expr_ref x_value(m.mk_eq(x, mod), m);
        expr_ref different(m.mk_not(m.mk_eq(x, ui)), m);
        expr* conjuncts[] = {u_value, v_value, x_value, different};
        expr_ref body(m.mk_and(conjuncts), m);
        expr_ref original(m.mk_exists(1, &integer, &name, body), m);
        solver_ref plain(mk_smt_solver(m, params_ref(), symbol()));
        plain->assert_expr(original);
        ENSURE(plain->check_sat(0, nullptr) == l_true);
        goal_ref input = alloc(goal, m, proofs, true, false);
        input->assert_expr(original);
        tactic_ref qe = mk_qe_tactic(m);
        tactic_ref smt = mk_smt_tactic(m);
        tactic_ref pipeline = and_then(qe.get(), smt.get());
        model_ref model;
        labels_vec labels;
        proof_ref proof(m);
        expr_dependency_ref core(m);
        std::string reason;
        ENSURE(check_sat(*pipeline, input, model, labels, proof, core, reason) == l_true);
    }
}

static void test_solve_eqs_proofs() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    expr_ref p(m.mk_const("p", m.mk_bool_sort()), m);
    expr_ref q(m.mk_const("q", m.mk_bool_sort()), m);
    expr_ref r(m.mk_const("r", m.mk_bool_sort()), m);
    expr_ref s(m.mk_const("s", m.mk_bool_sort()), m);
    expr_ref_vector assertions(m);

    auto check = [&]() {
        base_dependent_expr_state st(m);
        for (expr* f : assertions)
            st.add(dependent_expr(m, f, m.mk_asserted(f), nullptr));
        euf::solve_eqs solve(m, st);
        ENSURE(solve.supports_proofs());
        solve.reduce();
        ENSURE(st.inconsistent());
        check_simplifier_proofs(m, st, assertions);
    };

    assertions.push_back(m.mk_eq(p, q));
    assertions.push_back(m.mk_eq(q, r));
    assertions.push_back(m.mk_or(p, s));
    assertions.push_back(m.mk_not(r));
    assertions.push_back(m.mk_not(s));
    check();

    assertions.reset();
    assertions.push_back(m.mk_eq(m.mk_not(q), p));
    assertions.push_back(m.mk_not(q));
    assertions.push_back(m.mk_not(p));
    check();

    assertions.reset();
    assertions.push_back(m.mk_eq(p, m.mk_or(q, r)));
    assertions.push_back(m.mk_not(q));
    assertions.push_back(m.mk_not(r));
    assertions.push_back(p);
    check();

    arith_util a(m);
    expr_ref x(m.mk_const("x", a.mk_int()), m);
    assertions.reset();
    assertions.push_back(m.mk_eq(x, a.mk_int(3)));
    assertions.push_back(a.mk_lt(x, a.mk_int(2)));
    check();

    assertions.reset();
    assertions.push_back(m.mk_eq(p, q));
    base_dependent_expr_state st(m);
    st.add(dependent_expr(m, assertions.get(0), m.mk_asserted(assertions.get(0)), nullptr));
    euf::solve_eqs solve(m, st);
    solve.reduce();
    check_simplifier_proofs(m, st, assertions);
    st.flatten_suffix();
    st.advance_qhead();
    assertions.push_back(m.mk_not(p));
    assertions.push_back(q);
    for (unsigned i = 1; i < assertions.size(); ++i)
        st.add(dependent_expr(m, assertions.get(i), m.mk_asserted(assertions.get(i)), nullptr));
    expr_ref_vector assumptions(m);
    st.replay(st.qhead(), assumptions);
    check_simplifier_proofs(m, st, assertions);
    solve.reduce();
    ENSURE(st.inconsistent());
    check_simplifier_proofs(m, st, assertions);
}

static void test_solve_eqs_macro_constants() {
    char const* definitions[] = {
        "(define-fun B () Int x)",
        "(define-fun B ((y Int)) Int (+ x y))",
        "(define-fun-rec f ((y Int)) Int (ite (= y 0) x (f (- y 1))))"
    };
    for (unsigned i = 0; i < 3; ++i) {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        std::string source = "(declare-const x Int)";
        source += definitions[i];
        source += "(assert (= x 0))";
        Z3_ast_vector assertions = Z3_parse_smtlib2_string(ctx, source.c_str(), 0, nullptr, nullptr,
                                                        0, nullptr, nullptr);
        Z3_ast_vector_inc_ref(ctx, assertions);
        Z3_goal goal = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_inc_ref(ctx, goal);
        Z3_goal_assert(ctx, goal, Z3_ast_vector_get(ctx, assertions, 0));
        Z3_tactic tactic = Z3_mk_tactic(ctx, "solve-eqs");
        Z3_tactic_inc_ref(ctx, tactic);
        Z3_apply_result result = Z3_tactic_apply(ctx, tactic, goal);
        Z3_apply_result_inc_ref(ctx, result);
        ENSURE(Z3_apply_result_get_num_subgoals(ctx, result) == 1);
        Z3_goal subgoal = Z3_apply_result_get_subgoal(ctx, result, 0);
        ENSURE(Z3_goal_size(ctx, subgoal) == (i == 2 ? 1 : 0));
        Z3_apply_result_dec_ref(ctx, result);
        Z3_tactic_dec_ref(ctx, tactic);
        Z3_goal_dec_ref(ctx, goal);
        Z3_ast_vector_dec_ref(ctx, assertions);
        Z3_del_context(ctx);
    }
}

// solve-eqs must honor solve_eqs_max_occs: a variable with more occurrences
// than the bound is not eliminated. Occurrences are argument positions in
// distinct subterms, and the defining equation counts (the QF_BV preamble
// sets the bound to 2 for conservative Gaussian elimination).
static void test_solve_eqs_max_occs() {
    // xx occurs in its definition and in three other formulas.
    // yy occurs in its definition and in one other formula.
    char const* source =
        "(declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8))"
        "(declare-const xx (_ BitVec 8)) (declare-const yy (_ BitVec 8))"
        "(assert (= xx (bvadd a b)))"
        "(assert (bvult xx #x10)) (assert (bvult #x01 xx)) (assert (distinct xx b))"
        "(assert (= yy (bvmul a b))) (assert (bvult yy #x20))"
        // a and b occur often enough that only xx and yy are candidates.
        "(assert (distinct a b)) (assert (bvult a #x05))";
    // Returns the printed result goal of solve-eqs with the given bound.
    auto run = [&](unsigned max_occs) {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        Z3_ast_vector assertions = Z3_parse_smtlib2_string(ctx, source, 0, nullptr, nullptr,
                                                        0, nullptr, nullptr);
        Z3_ast_vector_inc_ref(ctx, assertions);
        Z3_goal goal = Z3_mk_goal(ctx, false, false, false);
        Z3_goal_inc_ref(ctx, goal);
        for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions); ++i)
            Z3_goal_assert(ctx, goal, Z3_ast_vector_get(ctx, assertions, i));
        Z3_params p = Z3_mk_params(ctx);
        Z3_params_inc_ref(ctx, p);
        Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "solve_eqs_max_occs"), max_occs);
        Z3_tactic tactic = Z3_tactic_using_params(ctx, Z3_mk_tactic(ctx, "solve-eqs"), p);
        Z3_tactic_inc_ref(ctx, tactic);
        Z3_apply_result result = Z3_tactic_apply(ctx, tactic, goal);
        Z3_apply_result_inc_ref(ctx, result);
        ENSURE(Z3_apply_result_get_num_subgoals(ctx, result) == 1);
        std::string out = Z3_goal_to_string(ctx, Z3_apply_result_get_subgoal(ctx, result, 0));
        Z3_apply_result_dec_ref(ctx, result);
        Z3_tactic_dec_ref(ctx, tactic);
        Z3_params_dec_ref(ctx, p);
        Z3_goal_dec_ref(ctx, goal);
        Z3_ast_vector_dec_ref(ctx, assertions);
        Z3_del_context(ctx);
        return out;
    };
    auto has = [](std::string const& goal, char const* name) { return goal.find(name) != std::string::npos; };
    // Unbounded: both xx and yy are eliminated.
    std::string unbounded = run(UINT_MAX);
    ENSURE(!has(unbounded, "xx") && !has(unbounded, "yy"));
    // Bound 2: yy (2 occurrences) is eliminated; xx (4 occurrences) is kept.
    std::string bounded = run(2);
    ENSURE(has(bounded, "xx") && !has(bounded, "yy"));
}

static void test_solve_eqs_proof_scope() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        arith_util a(m);
        expr_ref x(m.mk_const("x", a.mk_int()), m);
        expr_ref y(m.mk_const("y", a.mk_int()), m);
        expr_ref lhs(a.mk_add(x, y), m);
        expr_ref rhs(a.mk_int(0), m);
        expr_ref equation(m.mk_eq(lhs, rhs), m);
        base_dependent_expr_state st(m);
        st.add(dependent_expr(m, equation, proofs ? m.mk_asserted(equation) : nullptr, nullptr));
        euf::solve_eqs solve(m, st);
        solve.reduce();
        if (proofs) {
            ENSURE(st[0].fml() == equation);
            expr_ref_vector assertions(m);
            assertions.push_back(equation);
            check_simplifier_proofs(m, st, assertions);
        }
        else
            ENSURE(m.is_true(st[0].fml()));
    }
}

static void test_flatten_suffix_proofs() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    expr_ref p(m.mk_const("p", m.mk_bool_sort()), m);
    expr_ref q(m.mk_const("q", m.mk_bool_sort()), m);
    expr_ref r(m.mk_const("r", m.mk_bool_sort()), m);
    expr_ref_vector assertions(m);
    assertions.push_back(m.mk_and(p, m.mk_not(m.mk_or(m.mk_not(q), r))));
    base_dependent_expr_state st(m);
    st.add(dependent_expr(m, assertions.get(0), m.mk_asserted(assertions.get(0)), nullptr));
    st.flatten_suffix();
    ENSURE(st.qtail() == 3);
    check_simplifier_proofs(m, st, assertions);
}

// Exercises `lambda_simplifier`'s new proof production end-to-end:
// - a chain of two nested macros (c2's body mentions c1), so `resolve`
//   actually builds a `PR_DEMODULATION` + transitivity chain;
// - a macro's own defining equation gets collapsed to `true` via
//   `PR_IFF_TRUE`;
// - a separate use-site formula gets rewritten by substituting the fully
//   resolved macro bodies, combined with the `th_rewriter`'s own proof.
// `check_simplifier_proofs` independently re-checks every resulting proof
// object via `proof_checker` (including, for `PR_DEMODULATION`, actually
// re-deriving the substitution and comparing results structurally).
static void test_lambda_simplifier_proofs() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    array_util au(m);
    arith_util a(m);
    sort* I = a.mk_int();
    sort* arr = au.mk_array_sort(I, I);

    expr_ref c1(m.mk_const("c1", arr), m);
    expr_ref c2(m.mk_const("c2", arr), m);
    expr_ref y(m.mk_const("y", I), m);
    symbol xn("x");

    // c1 = (lambda ((x Int)) 0)
    expr_ref zero(a.mk_int(0), m);
    expr_ref lam1(m.mk_lambda(1, &I, &xn, zero.get()), m);
    expr_ref def1(m.mk_eq(c1.get(), lam1.get()), m);

    // c2 = (lambda ((x Int)) (select c1 x))   -- nested macro reference
    expr_ref sel_c1x(au.mk_select(c1.get(), m.mk_var(0, I)), m);
    expr_ref lam2(m.mk_lambda(1, &I, &xn, sel_c1x.get()), m);
    expr_ref def2(m.mk_eq(c2.get(), lam2.get()), m);

    // use site: (select c2 y) = 0
    expr_ref use(m.mk_eq(au.mk_select(c2.get(), y.get()), zero.get()), m);

    expr_ref_vector assertions(m);
    assertions.push_back(def1);
    assertions.push_back(def2);
    assertions.push_back(use);

    base_dependent_expr_state st(m);
    for (expr* f : assertions)
        st.add(dependent_expr(m, f, m.mk_asserted(f), nullptr));

    lambda_simplifier lam_simp(m, params_ref(), st);
    ENSURE(lam_simp.supports_proofs());
    lam_simp.reduce();

    // both macro-defining equations collapse to `true`.
    ENSURE(m.is_true(st[0].fml()));
    ENSURE(m.is_true(st[1].fml()));
    // the use site got rewritten (beta-reduced/simplified) away from its
    // original shape.
    ENSURE(st[2].fml() != use.get());

    check_simplifier_proofs(m, st, assertions);
}

// Exercises `demodulator_simplifier`'s new proof production end-to-end:
// - the demodulator `forall x. f(x) = x + 1` justifies rewriting a ground
//   use site `f(2) != 3` down to `false` via a `PR_QUANT_INST` instance
//   combined (via unit resolution and congruence/transitivity) with the
//   th_rewriter's own arithmetic normalization proof;
// - a second, `not`-shaped demodulator (`forall x. not p(x) <-> x > 0`,
//   i.e. one of `demodulator_util::is_demodulator`'s reshaped cases) is
//   also exercised, forcing `mk_instance_proof`'s `mk_rewrite` bridge path.
// `check_simplifier_proofs` independently re-checks every resulting proof
// object via `proof_checker`.
static void test_demodulator_simplifier_proofs() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    arith_util a(m);
    sort* I = a.mk_int();
    sort* dom1[1] = { I };
    func_decl_ref f(m.mk_func_decl(symbol("f"), 1, dom1, I), m);
    symbol xn("x");

    // forall x. f(x) = x + 1
    var_ref x(m.mk_var(0, I), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref fx(m.mk_app(f, x.get()), m);
    expr_ref rhs(a.mk_add(x, one), m);
    expr_ref def(m.mk_eq(fx, rhs), m);
    quantifier_ref q(m.mk_forall(1, &I, &xn, def), m);

    // use site: not (f(2) = 3)   -- should rewrite to `false`.
    expr_ref two(a.mk_int(2), m);
    expr_ref three(a.mk_int(3), m);
    expr_ref f2(m.mk_app(f, two.get()), m);
    expr_ref use(m.mk_not(m.mk_eq(f2, three)), m);

    expr_ref_vector assertions(m);
    assertions.push_back(q);
    assertions.push_back(use);

    base_dependent_expr_state st(m);
    demodulator_simplifier demod(m, params_ref(), st);
    ENSURE(demod.supports_proofs());
    st.add(dependent_expr(m, q, m.mk_asserted(q), nullptr));
    demod.reduce();
    st.advance_qhead();
    st.add(dependent_expr(m, use, m.mk_asserted(use), nullptr));
    demod.reduce();

    ENSURE(m.is_false(st[1].fml()));
    check_simplifier_proofs(m, st, assertions);
}

static void test_demodulator_quantified_proofs() {
    for (bool proofs : {false, true}) {
        for (bool nested : {false, true}) {
            ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
            reg_decl_plugins(m);
            arith_util a(m);
            sort* integer = a.mk_int();
            func_decl_ref f(m.mk_func_decl(symbol("demod-f"), integer, integer), m);
            symbol name("x"), bool_name("b");
            expr_ref x(m.mk_var(0, integer), m);
            expr_ref fx(m.mk_app(f, x.get()), m);
            expr_ref definition(m.mk_eq(fx, x), m);
            expr_ref use(a.mk_gt(fx, x), m);
            if (nested) {
                expr_ref outer(m.mk_var(1, integer), m), one(a.mk_int(1), m);
                expr_ref arg(a.mk_add(outer, one), m);
                expr_ref farg(m.mk_app(f, arg.get()), m);
                sort* boolean = m.mk_bool_sort();
                expr_ref b(m.mk_var(0, boolean), m);
                expr_ref comparison(a.mk_gt(farg, arg), m);
                expr_ref body(m.mk_implies(b, comparison), m);
                use = m.mk_forall(1, &boolean, &bool_name, body);
            }
            expr_ref_vector assertions(m);
            assertions.push_back(m.mk_forall(1, &integer, &name, definition));
            assertions.push_back(m.mk_forall(1, &integer, &name, use));
            base_dependent_expr_state state(m);
            demodulator_simplifier demod(m, params_ref(), state);
            state.add(dependent_expr(m, assertions.get(0), proofs ? m.mk_asserted(assertions.get(0)) : nullptr, nullptr));
            demod.reduce();
            state.advance_qhead();
            state.add(dependent_expr(m, assertions.get(1), proofs ? m.mk_asserted(assertions.get(1)) : nullptr, nullptr));
            demod.reduce();
            ENSURE(state[1].fml() != assertions.get(1));
            ENSURE(!occurs(f, state[1].fml()));
            if (!nested) {
                ENSURE(m.is_false(state[1].fml()));
            }
            if (proofs)
                check_simplifier_proofs(m, state, assertions);
        }
    }
}

static void test_pull_nested_quantifier_proofs() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        sort* boolean = m.mk_bool_sort();
        symbol x_name("x"), y_name("y");
        expr_ref x(m.mk_var(0, boolean), m), outer(m.mk_var(1, boolean), m);
        func_decl_ref predicate(m.mk_func_decl(symbol("quant-p"), boolean, boolean), m);
        expr_ref px(m.mk_app(predicate.get(), x), m);
        expr_ref not_px(m.mk_not(px), m), double_not_px(m.mk_not(not_px), m);
        sort* domains[] = {boolean, boolean};
        func_decl_ref relation(m.mk_func_decl(symbol("quant-r"), 2, domains, boolean), m);
        expr_ref rxy(m.mk_app(relation.get(), outer, x), m);
        expr_ref inner_exists(m.mk_exists(1, &boolean, &y_name, rxy), m);
        expr_ref inner_forall(m.mk_forall(1, &boolean, &y_name, rxy), m);
        expr_ref_vector originals(m);
        originals.push_back(m.mk_exists(1, &boolean, &x_name, px));
        originals.push_back(m.mk_exists(1, &boolean, &x_name, double_not_px));
        originals.push_back(m.mk_forall(1, &boolean, &x_name, inner_exists));
        originals.push_back(m.mk_exists(1, &boolean, &x_name, inner_forall));
        pull_nested_quant rewrite(m);
        for (expr* original : originals) {
            expr_ref result(m);
            proof_ref pr(m);
            rewrite(original, result, pr);
            ENSURE(result != original);
            if (proofs) {
                expr_ref equality(m.mk_eq(original, result), m);
                ENSURE(pr && m.get_fact(pr) == equality);
            }
            base_dependent_expr_state state(m);
            state.add(dependent_expr(m, original, proofs ? m.mk_asserted(original) : nullptr, nullptr));
            pull_nested_quantifiers_simplifier simplify(m, params_ref(), state);
            simplify.reduce();
            ENSURE(state[0].fml() == result);
            if (proofs) {
                expr_ref_vector assertions(m);
                assertions.push_back(original);
                check_simplifier_proofs(m, state, assertions);
            }
        }
    }
}

static void test_quantified_bool_literals() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        th_rewriter rw(m);
        sort* b = m.mk_bool_sort();
        symbol name("x");
        expr_ref x(m.mk_var(0, b), m);
        expr_ref p(m.mk_const("p", b), m);
        expr_ref result(m);
        proof_ref pr(m);
        for (bool universal : {false, true}) {
            for (bool negate_body : {false, true}) {
                for (bool negate_literal : {false, true}) {
                    expr_ref lit(negate_literal ? m.mk_not(x) : x.get(), m);
                    bool conjunction = universal != negate_body;
                    expr_ref body(conjunction ? m.mk_and(lit, p) : m.mk_or(lit, p), m);
                    if (negate_body)
                        body = m.mk_not(body);
                    quantifier_ref q(m.mk_quantifier(
                        universal ? forall_k : exists_k, 1, &b, &name, body), m);
                    rw(q, result, pr);
                    ENSURE(universal ? m.is_false(result) : m.is_true(result));
                    if (proofs) {
                        ENSURE(pr);
                        expr_ref equality(m.mk_eq(q, result), m);
                        ENSURE(m.get_fact(pr) == equality);
                        base_dependent_expr_state st(m);
                        st.add(dependent_expr(m, equality, pr, nullptr));
                        expr_ref_vector assertions(m);
                        check_simplifier_proofs(m, st, assertions);
                    }
                }
            }
        }

        func_decl_ref f(m.mk_func_decl(symbol("f"), b, b), m);
        expr_ref fx(m.mk_app(f.get(), x.get()), m);
        expr_ref outer(m.mk_var(1, b), m);
        expr_ref body(m.mk_or(outer, fx), m);
        quantifier_ref q(m.mk_exists(1, &b, &name, body), m);
        rw(q, result, pr);
        ENSURE(!m.is_true(result) && !m.is_false(result));

        body = m.mk_and(x, p);
        q = m.mk_lambda(1, &b, &name, body);
        rw(q, result, pr);
        ENSURE(is_lambda(result));
    }
}

static void test_nested_symbolic_rotations() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    for (unsigned width : { 3u, 4u, 24u }) {
        unsigned mask = (1u << width) - 1;
        Z3_sort sort = Z3_mk_bv_sort(ctx, width);
        Z3_ast vars[] = {
            Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), sort),
            Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), sort),
            Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "z"), sort)
        };
        auto rotate = [&](unsigned value, unsigned amount, bool left) {
            unsigned shift = amount % width;
            if (!left)
                shift = (width - shift) % width;
            return ((value << shift) | (value >> (width - shift))) & mask;
        };
        for (bool inner_left : { false, true }) {
            Z3_ast inner = inner_left ? Z3_mk_ext_rotate_left(ctx, vars[0], vars[1]) :
                                       Z3_mk_ext_rotate_right(ctx, vars[0], vars[1]);
            for (bool outer_left : { false, true }) {
                Z3_ast nested = outer_left ? Z3_mk_ext_rotate_left(ctx, inner, vars[2]) :
                                            Z3_mk_ext_rotate_right(ctx, inner, vars[2]);
                Z3_ast simplified = Z3_simplify(ctx, nested);
                for (unsigned amount : { 0u, mask }) {
                    Z3_ast values[] = {
                        Z3_mk_unsigned_int(ctx, 1, sort),
                        Z3_mk_unsigned_int(ctx, amount, sort),
                        Z3_mk_unsigned_int(ctx, 1, sort)
                    };
                    unsigned expected = rotate(rotate(1, amount, inner_left), 1, outer_left);
                    Z3_ast actual = Z3_substitute(ctx, simplified, 3, vars, values);
                    expect_simplifies_to(ctx, actual, Z3_mk_unsigned_int(ctx, expected, sort));
                }
            }
        }
    }
    Z3_del_context(ctx);
}

static void test_use_aware_replace_contains() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util seq(m);
    th_rewriter rw(m);

    expr_ref source(m.mk_fresh_const("source", seq.str.mk_string_sort()), m);
    expr_ref needle(seq.str.mk_string("T"), m);
    expr_ref replacement(seq.str.mk_string("t"), m);
    expr_ref observed(seq.str.mk_string("Y"), m);
    expr_ref replaced(seq.str.mk_replace(source, needle, replacement), m);

    expr_ref contains(seq.str.mk_contains(replaced, observed), m);
    expr_ref expected(seq.str.mk_contains(source, observed), m);
    rw(contains);
    rw(expected);
    ENSURE(contains == expected);

    expr_ref needle_contains(seq.str.mk_contains(replaced, needle), m);
    rw(needle_contains);
    ENSURE(needle_contains != seq.str.mk_contains(source, needle));

    expr_ref replacement_contains(seq.str.mk_contains(replaced, replacement), m);
    rw(replacement_contains);
    ENSURE(replacement_contains != seq.str.mk_contains(source, replacement));

    expr_ref multi(seq.str.mk_string("YY"), m);
    expr_ref multi_contains(seq.str.mk_contains(replaced, multi), m);
    rw(multi_contains);
    ENSURE(multi_contains != seq.str.mk_contains(source, multi));
}

static void test_seq_decimal_comparisons() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    th_rewriter rw(m);
    expr_ref_vector pin(m), cases(m);
    auto hold = [&](expr* e) { pin.push_back(e); return e; };
    auto integer = [&](rational const& n) { return hold(a.mk_numeral(n, true)); };
    expr_ref s(m.mk_const("decimal-s", u.str.mk_string_sort()), m);
    expr_ref n(m.mk_const("decimal-n", a.mk_int()), m);
    expr* stoi = hold(u.str.mk_stoi(s));
    enum class cmp { eq, ne, le, ge, lt, gt };
    auto compare = [&](cmp op, expr* x, expr* y) -> expr* {
        switch (op) {
        case cmp::eq: return hold(m.mk_eq(x, y));
        case cmp::ne: {
            expr* args[] = {x, y};
            return hold(m.mk_distinct(2, args));
        }
        case cmp::le: return hold(a.mk_le(x, y));
        case cmp::ge: return hold(a.mk_ge(x, y));
        case cmp::lt: return hold(a.mk_lt(x, y));
        case cmp::gt: return hold(a.mk_gt(x, y));
        default: UNREACHABLE(); return nullptr;
        }
    };
    for (char const* text : {"-2", "-1", "0", "9", "10", "255", "1000",
                            "123456789012345678901234567890"}) {
        expr* value = integer(rational(text));
        for (cmp op : {cmp::eq, cmp::ne, cmp::le, cmp::ge, cmp::lt, cmp::gt}) {
            expr* formula = compare(op, stoi, value);
            cases.push_back(formula);
            cases.push_back(hold(m.mk_not(formula)));
            cases.push_back(compare(op, value, stoi));
        }
    }
    expr* zero = integer(rational(0));
    expr* one = integer(rational(1));
    expr* first = hold(u.str.mk_substr(s, zero, one));
    expr* minus = hold(u.str.mk_string(zstring("-")));
    expr* negative = hold(m.mk_eq(first, minus));
    expr* len = hold(u.str.mk_length(s));
    expr* rest_len = hold(a.mk_sub(len, one));
    expr* rest = hold(u.str.mk_substr(s, one, rest_len));
    expr* rest_value = hold(u.str.mk_stoi(rest));
    expr* negated = hold(a.mk_uminus(rest_value));
    expr* signed_value = hold(m.mk_ite(negative, negated, stoi));
    expr* minus_one = integer(rational(-1));
    expr* reflected = hold(a.mk_mul(minus_one, signed_value));
    expr* five = integer(rational(5));
    expr* affine = hold(a.mk_add(reflected, five));
    expr* partial = hold(m.mk_ite(negative, n, stoi));
    for (int bound : {-1, 0, 1, 255}) {
        expr* value = integer(rational(bound));
        cases.push_back(compare(cmp::gt, signed_value, value));
        cases.push_back(compare(cmp::le, affine, value));
        cases.push_back(compare(cmp::eq, signed_value, value));
        cases.push_back(compare(cmp::ge, partial, value));
    }

    std::vector<zstring> words{zstring()};
    for (unsigned length = 1, begin = 0, end = 1; length <= 3; ++length) {
        unsigned next = static_cast<unsigned>(words.size());
        for (unsigned j = begin; j < end; ++j)
            for (unsigned ch : {'0', '2', '9', 'a'})
                words.push_back(words[j] + zstring(ch));
        begin = end;
        end = static_cast<unsigned>(words.size());
        ENSURE(next == begin);
    }
    for (char const* text : {"255", "256", "270", "299", "400", "999", "1000", "1001",
                            "0255", "00256", "0001000", "-12", "-a", "-", "0xff", "FF",
                            "123456789012345678901234567889",
                            "123456789012345678901234567890",
                            "123456789012345678901234567891",
                            "0123456789012345678901234567890",
                            "9999999999999999999999999999999"})
        words.push_back(zstring(text));
    words.push_back(zstring(0x0661u));
    words.push_back(zstring(0x1f600u));
    for (expr* formula : cases) {
        base_dependent_expr_state state(m);
        expr_ref label(m.mk_const("decimal-label", m.mk_bool_sort()), m);
        expr_dependency* dep = m.mk_leaf(label);
        state.add(dependent_expr(m, formula, nullptr, dep));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() != formula && state[0].dep() == dep);
        expr_ref rewritten(state[0].fml(), m);
        for (zstring const& word : words) {
            expr_ref value(u.str.mk_string(word), m);
            expr_safe_replace sub(m);
            sub.insert(s, value);
            sub.insert(n, five);
            expr_ref original(m), result(m);
            sub(formula, original);
            sub(rewritten, result);
            rw(original);
            rw(result);
            ENSURE(m.is_true(original) || m.is_false(original));
            ENSURE(original == result);
        }
    }
    {
        expr_ref t(m.mk_const("decimal-t", u.str.mk_string_sort()), m);
        expr* other = hold(u.str.mk_stoi(t));
        expr* sum = hold(a.mk_add(stoi, other));
        expr* relational = compare(cmp::eq, sum, n);
        expr* bound = integer(rational(255));
        expr* bounded = compare(cmp::gt, stoi, bound);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, bounded, nullptr, nullptr));
        state.add(dependent_expr(m, relational, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() != bounded && state[1].fml() == relational);
        expr_ref_vector conjuncts(m);
        flatten_and(state[0].fml(), conjuncts);
        ENSURE(conjuncts.contains(bounded));
        statistics st;
        simp.collect_statistics(st);
        bool rewritten = false;
        for (unsigned i = 0; i < st.size(); ++i)
            if (!strcmp(st.get_key(i), "seq-regular-stoi-rewritten"))
                rewritten = st.get_uint_value(i) == 1;
        ENSURE(rewritten);
        expr* valid = compare(cmp::ge, stoi, zero);
        base_dependent_expr_state coupled(m);
        coupled.add(dependent_expr(m, valid, nullptr, nullptr));
        coupled.add(dependent_expr(m, relational, nullptr, nullptr));
        seq_regular_simplifier keep_numeric(m, params_ref(), coupled);
        keep_numeric.reduce();
        ENSURE(coupled[0].fml() == valid && coupled[1].fml() == relational);
    }
    {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, cases.get(0), nullptr, nullptr));
        params_ref p;
        p.set_uint("seq_regular.max_steps", 1);
        seq_regular_simplifier simp(m, p, state);
        simp.reduce();
        ENSURE(state[0].fml() == cases.get(0));
    }
}

static void test_seq_bounded_conversions() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    th_rewriter rw(m);
    expr_ref s(m.mk_const("bounded-s", u.str.mk_string_sort()), m);
    expr_ref i(m.mk_const("bounded-i", a.mk_int()), m);
    expr_ref n(m.mk_const("bounded-n", a.mk_int()), m);
    expr_ref c(m.mk_const("bounded-c", m.mk_bool_sort()), m);
    expr_ref zero(a.mk_int(0), m), one(a.mk_int(1), m), minus_one(a.mk_int(-1), m);
    expr_ref at(u.str.mk_at(s, i), m);
    expr_ref x(u.str.mk_stoi(at), m);
    expr_ref relation(m.mk_eq(x, n), m);
    expr_ref lo(u.str.mk_string(zstring("0")), m), hi(u.str.mk_string(zstring("1")), m);
    expr_ref digit(u.re.mk_range(lo, hi), m);
    expr_ref binary(u.re.mk_plus(digit), m);
    expr_ref membership(u.re.mk_in_re(s, binary), m);
    expr_ref_vector cases(m), pin(m);
    auto hold = [&](expr* e) { pin.push_back(e); return e; };
    auto add = [&](expr* e) { cases.push_back(m.mk_and(relation, e)); };
    add(m.mk_true());
    add(membership);
    add(hold(m.mk_not(membership)));
    add(hold(m.mk_or(c, membership)));
    expr_ref literal(u.str.mk_string(zstring("27")), m);
    expr_ref exact(u.re.mk_to_re(literal), m);
    add(hold(u.re.mk_in_re(s, exact)));
    expr_ref repeated(u.re.mk_star(digit), m);
    add(hold(u.re.mk_in_re(s, repeated)));
    expr_ref excluded(u.re.mk_complement(binary), m);
    add(hold(u.re.mk_in_re(s, excluded)));
    expr_ref wide_hi(u.str.mk_string(zstring("9")), m);
    expr_ref decimal_digit(u.re.mk_range(lo, wide_hi), m);
    expr_ref decimal(u.re.mk_plus(decimal_digit), m);
    expr_ref intersection(u.re.mk_inter(decimal, binary), m);
    add(hold(u.re.mk_in_re(s, intersection)));
    expr_ref branch(a.mk_uminus(x), m);
    expr_ref signed_value(m.mk_ite(c, branch, x), m);
    expr_ref positive(a.mk_gt(signed_value, zero), m);
    expr_ref valid(m.mk_not(m.mk_eq(x, minus_one)), m);
    add(positive);
    expr_ref checked(m.mk_and(positive, valid), m);
    add(checked);
    expr_ref len(u.str.mk_length(s), m);
    expr_ref order(a.mk_lt(len, n), m);
    expr_ref minimum(m.mk_ite(order, len, n), m);
    expr_ref maximum(m.mk_ite(order, n, len), m);
    for (expr* term : {minimum.get(), maximum.get()}) {
        add(hold(a.mk_ge(term, one)));
        add(hold(a.mk_le(term, one)));
    }
    expr_ref part(u.str.mk_substr(s, i, one), m);
    expr_ref converted(u.str.mk_stoi(part), m);
    cases.push_back(m.mk_eq(converted, n));
    vector<zstring> words;
    for (char const* text : {"", "0", "1", "2", "5", "7", "9", "x", "-", "-1", "10", "27", "009"})
        words.push_back(zstring(text));
    words.push_back(zstring(0x0661u));
    words.push_back(zstring(0x1f600u));
    for (expr* formula : cases) {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, formula, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() != formula);
        expr_ref rewritten(state[0].fml(), m);
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen;
        todo.push_back(rewritten);
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (seen.contains(e)) continue;
            seen.insert(e);
            ENSURE(!u.str.is_stoi(e));
            if (is_app(e)) for (expr* arg : *to_app(e)) todo.push_back(arg);
        }
        for (auto const& word : words) {
            for (int offset : {-1, 0, 1, 3}) {
                for (int value = -2; value <= 10; ++value) {
                    for (bool choice : {false, true}) {
                        expr_ref text(u.str.mk_string(word), m);
                        expr_ref position(a.mk_int(offset), m), number(a.mk_int(value), m);
                        expr_safe_replace sub(m);
                        sub.insert(s, text);
                        sub.insert(i, position);
                        sub.insert(n, number);
                        sub.insert(c, choice ? m.mk_true() : m.mk_false());
                        expr_ref original(m), result(m);
                        sub(formula, original);
                        sub(rewritten, result);
                        rw(original);
                        rw(result);
                        ENSURE(m.is_true(original) || m.is_false(original));
                        ENSURE(original == result);
                    }
                }
            }
        }
    }
    {
        expr_ref t(m.mk_const("bounded-t", u.str.mk_string_sort()), m);
        expr_ref minus(u.str.mk_string(zstring("-")), m);
        expr_ref_vector inputs(m), outputs(m);
        inputs.push_back(relation);
        for (expr* source : {s.get(), t.get()}) {
            expr* length = hold(u.str.mk_length(source));
            expr* tail_length = hold(a.mk_sub(length, one));
            expr* tail = hold(u.str.mk_substr(source, one, tail_length));
            expr* tail_value = hold(u.str.mk_stoi(tail));
            expr* unsigned_value = hold(u.str.mk_stoi(source));
            expr* prefix = hold(u.str.mk_prefix(minus, source));
            expr* negative = hold(a.mk_uminus(tail_value));
            expr* signed_value = hold(m.mk_ite(prefix, negative, unsigned_value));
            inputs.push_back(a.mk_gt(signed_value, zero));
            expr* tail_invalid = hold(m.mk_eq(minus_one, tail_value));
            expr* tail_valid = hold(m.mk_ite(tail_invalid, m.mk_false(), m.mk_true()));
            expr* long_enough = hold(a.mk_gt(length, one));
            expr* negative_valid = hold(m.mk_and(tail_valid, long_enough));
            expr* unsigned_invalid = hold(m.mk_eq(minus_one, unsigned_value));
            expr* unsigned_valid = hold(m.mk_ite(unsigned_invalid, m.mk_false(), m.mk_true()));
            inputs.push_back(m.mk_ite(prefix, negative_valid, unsigned_valid));
        }
        base_dependent_expr_state state(m);
        for (expr* input : inputs) state.add(dependent_expr(m, input, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        for (unsigned j = 0; j < state.qtail(); ++j) outputs.push_back(state[j].fml());
        expr_ref original(mk_and(inputs), m), rewritten(mk_and(outputs), m);
        for (auto const& left : words) {
            for (auto const& right : words) {
                expr_ref l(u.str.mk_string(left), m), r(u.str.mk_string(right), m);
                expr_ref nine(a.mk_int(9), m);
                expr_safe_replace sub(m);
                sub.insert(s, l);
                sub.insert(t, r);
                sub.insert(i, zero);
                sub.insert(n, nine);
                expr_ref before(m), after(m);
                sub(original, before);
                sub(rewritten, after);
                rw(before);
                rw(after);
                ENSURE(m.is_true(before) || m.is_false(before));
                ENSURE(before == after);
            }
        }
    }
    {
        expr_ref domain_label(m.mk_const("bounded-domain", m.mk_bool_sort()), m);
        expr_ref value_label(m.mk_const("bounded-value", m.mk_bool_sort()), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, membership, nullptr, m.mk_leaf(domain_label)));
        state.add(dependent_expr(m, relation, nullptr, m.mk_leaf(value_label)));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ptr_vector<expr> premises;
        m.linearize(state[1].dep(), premises);
        ENSURE(premises.contains(domain_label) && premises.contains(value_label));
    }
    {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, relation, nullptr, nullptr));
        params_ref p;
        p.set_uint("seq_regular.max_steps", 1);
        seq_regular_simplifier simp(m, p, state);
        simp.reduce();
        ENSURE(state[0].fml() == relation);
    }
    {
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        simplifier_factory factory = [](ast_manager& m, params_ref const& p, dependent_expr_state& state) {
            return alloc(seq_regular_simplifier, m, p, state);
        };
        solver_ref solver(mk_simplifier_solver(mk_smt_solver(m, p, symbol()), &factory));
        expr_ref two(a.mk_int(2), m);
        expr_ref value(m.mk_eq(x, two), m);
        solver->assert_expr(value);
        ENSURE(solver->check_sat() == l_true);
        solver->push();
        solver->assert_expr(membership);
        ENSURE(solver->check_sat() == l_false);
        solver->pop(1);
        ENSURE(solver->check_sat() == l_true);
    }
}

static void test_seq_conversion_ranges() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    th_rewriter rw(m);
    expr_ref s(m.mk_const("range-s", u.str.mk_string_sort()), m);
    expr_ref choice(m.mk_const("range-choice", m.mk_bool_sort()), m);
    expr_ref zero(a.mk_int(0), m), one(a.mk_int(1), m), two(a.mk_int(2), m);
    expr_ref part(u.str.mk_substr(s, zero, two), m);
    expr_ref value(u.str.mk_stoi(part), m);
    expr_ref unbounded(u.str.mk_stoi(s), m);
    expr_ref negative(a.mk_uminus(unbounded), m);
    expr_ref signed_value(m.mk_ite(choice, negative, value), m);
    expr_ref threshold(a.mk_int(255), m);
    expr_ref impossible(a.mk_gt(signed_value, threshold), m);
    expr_ref label(m.mk_const("range-label", m.mk_bool_sort()), m);
    {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, impossible, nullptr, m.mk_leaf(label)));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state.inconsistent());
        ptr_vector<expr> premises;
        m.linearize(state[0].dep(), premises);
        ENSURE(premises.size() == 1 && premises[0] == label);
    }
    expr_ref_vector cases(m), pin(m);
    auto hold = [&](expr* e) { pin.push_back(e); return e; };
    for (int bound : {-2, -1, 0, 1, 98, 99, 100, 255}) {
        expr* number = hold(a.mk_int(bound));
        cases.push_back(a.mk_le(value, number));
        cases.push_back(a.mk_gt(value, number));
        cases.push_back(m.mk_eq(signed_value, number));
        cases.push_back(a.mk_le(signed_value, number));
    }
    expr* twice = hold(a.mk_mul(hold(a.mk_int(-2)), value));
    expr* shifted = hold(a.mk_add(twice, hold(a.mk_int(7))));
    cases.push_back(a.mk_lt(shifted, hold(a.mk_int(-191))));
    expr* length = hold(u.str.mk_length(part));
    cases.push_back(a.mk_gt(length, two));
    for (expr* formula : cases) {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, formula, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        expr_ref rewritten(state[0].fml(), m);
        for (char const* text : {"", "0", "00", "01", "09", "98", "99", "100", "999",
                                 "1000", "-", "-1", "x", "x9"}) {
            for (bool sign : {false, true}) {
                expr_ref word(u.str.mk_string(text), m);
                expr_safe_replace sub(m);
                sub.insert(s, word);
                sub.insert(choice, sign ? m.mk_true() : m.mk_false());
                expr_ref original(m), result(m);
                sub(formula, original);
                sub(rewritten, result);
                rw(original);
                rw(result);
                ENSURE(m.is_true(original) || m.is_false(original));
                ENSURE(original == result);
            }
        }
    }
    {
        expr_ref disjunction(m.mk_or(choice, impossible), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, disjunction, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == choice);
    }
    {
        expr_ref count(a.mk_add(one, one), m);
        expr_ref inner(u.str.mk_substr(s, zero, count), m);
        expr_ref len(u.str.mk_length(inner), m);
        expr_ref remaining(a.mk_sub(len, one), m);
        expr_ref suffix(u.str.mk_substr(inner, one, remaining), m);
        expr_ref positive(u.str.mk_stoi(inner), m);
        expr_ref parsed(u.str.mk_stoi(suffix), m);
        expr_ref negated(a.mk_uminus(parsed), m);
        expr_ref signed_part(m.mk_ite(choice, negated, positive), m);
        expr_ref too_large(a.mk_gt(signed_part, threshold), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, too_large, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state.inconsistent());
    }
    {
        expr_ref first(u.str.mk_at(s, zero), m), second(u.str.mk_at(s, one), m);
        expr_ref d0(u.str.mk_stoi(first), m), d1(u.str.mk_stoi(second), m);
        expr_ref valid0(a.mk_ge(d0, zero), m), valid1(a.mk_ge(d1, zero), m);
        expr_ref guarded(m.mk_ite(choice, one, d0), m);
        expr_ref sixteen(a.mk_int(16), m);
        expr_ref scaled(a.mk_mul(sixteen, guarded), m);
        expr_ref sum(a.mk_add(scaled, d1), m);
        expr_ref nonnegative(a.mk_ge(sum, zero), m);
        expr_ref difference(a.mk_sub(d0, d1), m), nine(a.mk_int(9), m);
        expr_ref bounded(a.mk_le(difference, nine), m);
        expr_ref ordered(a.mk_ge(difference, zero), m);
        for (expr* comparison : {nonnegative.get(), bounded.get(), ordered.get()}) {
            expr_ref_vector inputs(m);
            inputs.push_back(valid0);
            inputs.push_back(valid1);
            inputs.push_back(comparison);
            base_dependent_expr_state state(m);
            for (expr* input : inputs)
                state.add(dependent_expr(m, input, nullptr, nullptr));
            seq_regular_simplifier simp(m, params_ref(), state);
            simp.reduce();
            expr_ref original(mk_and(inputs), m);
            expr_ref_vector results(m);
            for (unsigned i = 0; i < state.qtail(); ++i)
                results.push_back(state[i].fml());
            expr_ref rewritten(mk_and(results), m);
            if (comparison != ordered) {
                expr *source, *language;
                ENSURE(u.str.is_in_re(state[0].fml(), source, language) && source == s);
            }
            for (char const* text : {"", "0", "9", "x", "90", "09", "99", "01", "123", "x9"}) {
                for (bool sign : {false, true}) {
                    expr_ref word(u.str.mk_string(text), m);
                    expr_safe_replace sub(m);
                    sub.insert(s, word);
                    sub.insert(choice, sign ? m.mk_true() : m.mk_false());
                    expr_ref expected(m), actual(m);
                    sub(original, expected);
                    sub(rewritten, actual);
                    rw(expected);
                    rw(actual);
                    ENSURE(m.is_true(expected) || m.is_false(expected));
                    ENSURE(actual == expected);
                }
            }
        }
    }
}

static void test_seq_regular_definitions() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    th_rewriter rw(m);
    expr_ref s(m.mk_const("defined-s", u.str.mk_string_sort()), m);
    expr_ref h(m.mk_const("defined-head", s->get_sort()), m);
    expr_ref t(m.mk_const("defined-tail", s->get_sort()), m);
    expr_ref c(m.mk_const("defined-character", s->get_sort()), m);
    expr_ref zero(a.mk_int(0), m), one(a.mk_int(1), m);
    expr_ref colon(u.str.mk_string(":"), m), alphabet(u.str.mk_string("aX"), m);
    expr_ref dot(u.str.mk_string("."), m);
    expr_ref index(u.str.mk_index(s, colon, zero), m);
    expr_ref after(a.mk_add(index, one), m);
    expr_ref len(u.str.mk_length(s), m);
    expr_ref rest(a.mk_sub(len, after), m);
    expr_ref head(u.str.mk_substr(s, zero, index), m);
    expr_ref tail(u.str.mk_substr(s, after, rest), m);
    expr_ref character(u.str.mk_at(h, zero), m);
    expr_ref_vector definitions(m), inputs(m), pin(m);
    definitions.push_back(m.mk_eq(h, head));
    definitions.push_back(m.mk_eq(t, tail));
    definitions.push_back(m.mk_eq(c, character));
    inputs.append(definitions);
    inputs.push_back(u.str.mk_contains(alphabet, c));
    pin.push_back(u.str.mk_length(h));
    inputs.push_back(m.mk_eq(pin.back(), one));
    pin.push_back(u.str.mk_length(t));
    inputs.push_back(a.mk_gt(pin.back(), zero));
    pin.push_back(u.str.mk_contains(t, dot));
    inputs.push_back(m.mk_not(pin.back()));
    expr_ref original(mk_and(inputs), m);
    for (bool labeled : {false, true}) {
        base_dependent_expr_state state(m);
        for (expr* input : inputs) {
            expr_ref label(m.mk_fresh_const("definition-label", m.mk_bool_sort()), m);
            pin.push_back(label);
            state.add(dependent_expr(m, input, nullptr, labeled ? m.mk_leaf(label) : nullptr));
        }
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        expr_ref rewritten(state[0].fml(), m);
        ENSURE(rewritten != inputs[0]);
        expr_ref_vector conjuncts(m);
        flatten_and(rewritten, conjuncts);
        for (expr* definition : definitions) ENSURE(conjuncts.contains(definition));
        bool membership = false;
        for (expr* conjunct : conjuncts) {
            expr *source, *language;
            membership |= u.str.is_in_re(conjunct, source, language) && source == s;
        }
        ENSURE(membership);
        if (labeled) {
            ptr_vector<expr> premises;
            m.linearize(state[0].dep(), premises);
            ENSURE(premises.size() == inputs.size());
        }
        for (char const* text : {"", "a", "a:", ":a", "a:b", "X:q", "a:b.c",
                                 "a:b:c", "b:q", "aa:b"}) {
            for (bool wrong_character : {false, true}) {
                expr_ref word(u.str.mk_string(text), m);
                expr_safe_replace sub(m);
                sub.insert(s, word);
                for (expr* definition : definitions) {
                    app* eq = to_app(definition);
                    expr_ref value(m);
                    sub(eq->get_arg(1), value);
                    rw(value);
                    if (wrong_character && eq->get_arg(0) == c)
                        value = u.str.mk_string("z");
                    sub.insert(eq->get_arg(0), value);
                }
                expr_ref expected(m), actual(m);
                sub(original, expected);
                sub(rewritten, actual);
                rw(expected);
                rw(actual);
                ENSURE(m.is_true(expected) || m.is_false(expected));
                ENSURE(actual == expected);
            }
        }
    }
    {
        expr_ref other(m.mk_const("defined-other", s->get_sort()), m);
        expr_ref relation(m.mk_eq(s, other), m);
        base_dependent_expr_state state(m);
        for (expr* input : inputs)
            state.add(dependent_expr(m, input, nullptr, nullptr));
        state.add(dependent_expr(m, relation, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        for (unsigned i = 0; i < inputs.size(); ++i)
            ENSURE(state[i].fml() == inputs[i]);
        ENSURE(state[inputs.size()].fml() == relation);
    }
    {
        expr_ref recursive(u.str.mk_at(h, zero), m);
        expr_ref definition(m.mk_eq(h, recursive), m);
        expr_ref observation(u.str.mk_contains(alphabet, h), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, definition, nullptr, nullptr));
        state.add(dependent_expr(m, observation, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == definition && state[1].fml() == observation);
    }
    {
        expr_ref flag(m.mk_const("conditional-definition", m.mk_bool_sort()), m);
        expr_ref conditional(m.mk_or(flag, definitions.get(0)), m);
        expr_ref observation(u.str.mk_contains(alphabet, character), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, conditional, nullptr, nullptr));
        state.add(dependent_expr(m, observation, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == conditional && state[1].fml() == observation);
    }
}

static void test_seq_regular_group_order() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    expr_ref needle(u.str.mk_string("a"), m);
    expr_ref_vector observations(m);
    for (char const* name : {"regular-order-x", "regular-order-y", "regular-order-z"}) {
        expr_ref subject(m.mk_const(name, u.str.mk_string_sort()), m);
        observations.push_back(u.str.mk_contains(subject, needle));
    }
    for (bool conjunction : {false, true}) {
        unsigned order[] = {0, 1, 2};
        expr_ref expected(m);
        do {
            expr_ref_vector args(m);
            for (unsigned i : order)
                args.push_back(observations.get(i));
            expr_ref input(conjunction ? m.mk_and(args) : m.mk_or(args), m);
            base_dependent_expr_state state(m);
            state.add(dependent_expr(m, input, nullptr, nullptr));
            seq_regular_simplifier simp(m, params_ref(), state);
            simp.reduce();
            ENSURE(state[0].fml() != input);
            if (!expected)
                expected = state[0].fml();
            else
                ENSURE(state[0].fml() == expected);
        }
        while (std::next_permutation(std::begin(order), std::end(order)));
    }
}

static void test_seq_regular() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    {
        expr_ref shared(m.mk_const("regular-shared", m.mk_bool_sort()), m);
        for (unsigned i = 0; i < 40; ++i) {
            expr_ref negated(m.mk_not(shared), m);
            shared = m.mk_or(shared, negated);
        }
        scoped_rlimit limit(m.limit(), 200);
        ENSURE(!seq_regular_simplifier::has_string_terms(m, shared));
        ENSURE(m.inc());
    }
    expr_ref_vector pin(m), cases(m);
    auto hold = [&](expr* e) { pin.push_back(e); return e; };
    auto text = [&](char const* s) { return hold(u.str.mk_string(zstring(s))); };
    auto integer = [&](int n) { return hold(a.mk_int(n)); };
    auto contains = [&](expr* s, char const* t) { return hold(u.str.mk_contains(s, text(t))); };
    auto eq = [&](expr* s, char const* t) { return hold(m.mk_eq(s, text(t))); };
    expr_ref s(m.mk_const("regular-s", u.str.mk_string_sort()), m);
    expr* a_word = text("a");
    expr* b_word = text("b");
    expr* colon = text(":");
    expr* empty = text("");
    expr* zero = integer(0);
    expr* one = integer(1);
    expr* len = hold(u.str.mk_length(s));
    expr* index = hold(u.str.mk_index(s, colon, zero));
    expr* after = hold(a.mk_add(index, one));
    expr* tail_len = hold(a.mk_sub(len, after));
    expr* prefix = hold(u.str.mk_substr(s, zero, index));
    expr* through_len = hold(a.mk_add(index, one));
    expr* through = hold(u.str.mk_substr(s, zero, through_len));
    expr* tail = hold(u.str.mk_substr(s, after, tail_len));
    expr* from_len = hold(a.mk_sub(len, index));
    expr* from = hold(u.str.mk_substr(s, index, from_len));
    expr* last_pos = hold(a.mk_sub(len, one));
    expr* last = hold(u.str.mk_at(s, last_pos));
    expr* first = hold(u.str.mk_at(s, zero));
    expr* trim = hold(u.str.mk_substr(s, zero, last_pos));
    expr* fixed = hold(u.str.mk_substr(s, one, integer(2)));
    expr* drop_len = hold(a.mk_sub(len, one));
    expr* drop = hold(u.str.mk_substr(s, one, drop_len));
    expr* replaced = hold(u.str.mk_replace(s, a_word, b_word));
    expr* twice = hold(u.str.mk_replace(replaced, a_word, b_word));
    for (expr* part : {prefix, through, tail, from, last, first, trim, fixed, drop}) {
        cases.push_back(contains(part, "a"));
        expr* no_a = hold(m.mk_not(contains(part, "a")));
        expr* no_b = hold(m.mk_not(contains(part, "b")));
        cases.push_back(m.mk_and(no_a, no_b));
        cases.push_back(eq(part, ""));
    }
    cases.push_back(hold(m.mk_not(contains(twice, "a"))));
    cases.push_back(contains(replaced, "a"));
    cases.push_back(eq(replaced, "b"));
    cases.push_back(eq(replaced, "ab"));
    cases.push_back(eq(replaced, "ba"));
    cases.push_back(eq(replaced, ""));
    expr* replaced_index = hold(u.str.mk_index(replaced, colon, zero));
    expr* replaced_after = hold(a.mk_add(replaced_index, one));
    expr* replaced_len = hold(u.str.mk_length(replaced));
    expr* replaced_tail_len = hold(a.mk_sub(replaced_len, replaced_after));
    expr* replaced_tail = hold(u.str.mk_substr(replaced, replaced_after, replaced_tail_len));
    cases.push_back(contains(replaced_tail, ":"));
    expr* a_range = hold(u.re.mk_range(a_word, a_word));
    expr* b_range = hold(u.re.mk_range(b_word, b_word));
    expr* ab_range = hold(u.re.mk_union(a_range, b_range));
    expr* ab_loop = hold(u.re.mk_loop(ab_range, 1, 2));
    expr* colon_re = hold(u.re.mk_to_re(colon));
    expr* ab_suffix = hold(u.re.mk_concat(ab_loop, colon_re));
    expr* surrounded = hold(u.re.mk_concat(colon_re, ab_suffix));
    cases.push_back(hold(u.re.mk_in_re(replaced, surrounded)));
    expr* erase = hold(u.str.mk_replace(s, text("aa"), empty));
    cases.push_back(eq(erase, "b"));
    expr* prepend = hold(u.str.mk_replace(s, empty, a_word));
    cases.push_back(eq(prepend, "ab"));
    expr* constant_prefix = hold(u.str.mk_concat(text("a"), s));
    expr* constant_suffix = hold(u.str.mk_concat(s, text("a")));
    cases.push_back(eq(constant_prefix, "ab"));
    cases.push_back(eq(constant_suffix, "ba"));
    cases.push_back(hold(a.mk_ge(index, integer(-1))));
    expr* remaining = hold(a.mk_sub(len, index));
    cases.push_back(hold(a.mk_ge(remaining, one)));
    expr* prefix_a = contains(prefix, "a");
    expr* last_empty = eq(last, "");
    cases.push_back(hold(m.mk_or(prefix_a, last_empty)));
    expr* tail_b = contains(tail, "b");
    expr* both_parts = hold(m.mk_and(prefix_a, tail_b));
    cases.push_back(hold(m.mk_not(both_parts)));
    expr* conditional = hold(m.mk_ite(prefix_a, tail_b, last_empty));
    cases.push_back(conditional);
    cases.push_back(hold(m.mk_not(conditional)));
    expr* first_a = contains(first, "a");
    expr* first_b = eq(first, "b");
    cases.push_back(hold(u.str.mk_contains(text("aX"), first)));
    cases.push_back(hold(u.str.mk_contains(empty, first)));
    expr* first_either = hold(m.mk_or(first_a, first_b));
    cases.push_back(first_either);
    cases.push_back(hold(m.mk_and(first_either, prefix_a)));
    expr* impossible_first = hold(m.mk_and(first_a, first_b));
    cases.push_back(hold(m.mk_or(impossible_first, tail_b)));
    expr* fixed_b = eq(fixed, "b");
    cases.push_back(hold(m.mk_ite(first_a, conditional, fixed_b)));
    cases.push_back(hold(a.mk_lt(len, integer(2))));
    cases.push_back(hold(a.mk_ge(len, integer(3))));
    cases.push_back(contains(constant_prefix, "b"));
    cases.push_back(hold(m.mk_not(contains(constant_suffix, "b"))));
    expr* reinsert = hold(u.str.mk_replace(s, a_word, text("aa")));
    expr* delete_a = hold(u.str.mk_replace(s, a_word, empty));
    cases.push_back(hold(m.mk_not(contains(reinsert, "a"))));
    cases.push_back(hold(m.mk_not(contains(delete_a, "a"))));
    expr* split_rejoin = hold(u.str.mk_replace(through, colon, b_word));
    split_rejoin = hold(u.str.mk_concat(split_rejoin, tail));
    cases.push_back(eq(split_rejoin, "ab"));

    std::vector<zstring> words{zstring()};
    for (unsigned length = 1, begin = 0, end = 1; length <= 4; ++length) {
        unsigned next = static_cast<unsigned>(words.size());
        for (unsigned j = begin; j < end; ++j)
            for (unsigned ch : {97u, 98u, 58u, 10u, 0x1f600u})
                words.push_back(words[j] + zstring(ch));
        begin = end; end = static_cast<unsigned>(words.size());
        ENSURE(next == begin);
    }
    th_rewriter rw(m);
    for (int width : {2, 3}) {
        expr* bounded = hold(u.str.mk_substr(s, zero, integer(width)));
        expr* bounded_length = hold(u.str.mk_length(bounded));
        expr_ref remaining(a.mk_sub(bounded_length, one), m);
        rw(remaining);
        expr* bounded_tail = hold(u.str.mk_substr(bounded, one, remaining));
        cases.push_back(contains(bounded_tail, "a"));
        cases.push_back(eq(bounded_tail, ""));
    }
    {
        expr* expanded = hold(u.str.mk_replace(s, a_word, text("bb")));
        expr* character = hold(u.re.mk_full_char(colon_re->get_sort()));
        expr* two_chars = hold(u.re.mk_loop(character, 2, 2));
        expr* formula = hold(u.re.mk_in_re(expanded, two_chars));
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, formula, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == formula);
    }
    for (expr* formula : cases) {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, formula, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        if (state[0].fml() == formula)
            std::cerr << "regularization did not apply: " << mk_pp(formula, m) << "\n";
        ENSURE(state[0].fml() != formula);
        expr_ref rewritten(state[0].fml(), m);
        for (auto const& word : words) {
            expr_ref value(u.str.mk_string(word), m);
            expr_safe_replace sub(m);
            sub.insert(s, value);
            expr_ref original(m), result(m);
            sub(formula, original);
            sub(rewritten, result);
            rw(original);
            rw(result);
            ENSURE(m.is_true(original) || m.is_false(original));
            ENSURE(original == result);
        }
    }
    {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, conditional, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        expr *source, *language;
        ENSURE(u.str.is_in_re(state[0].fml(), source, language) && source == s);
    }
    {
        base_dependent_expr_state state(m);
        expr_ref no_a(m.mk_not(contains(prefix, "a")), m);
        expr_ref no_b(m.mk_not(contains(prefix, "b")), m);
        state.add(dependent_expr(m, no_a, nullptr, nullptr));
        state.add(dependent_expr(m, no_b, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() != no_a && m.is_true(state[1].fml()));
        expr* root;
        expr* language;
        ENSURE(u.str.is_in_re(state[0].fml(), root, language) && root == s);
    }
    {
        expr_ref binding(eq(s, "ab:"), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, binding, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == binding);

        state.add(dependent_expr(m, contains(prefix, "a"), nullptr, nullptr));
        simp.reduce();
        expr_ref_vector conjuncts(m);
        flatten_and(state[0].fml(), conjuncts);
        bool retained = false;
        for (expr* conjunct : conjuncts)
            retained |= conjunct == binding;
        ENSURE(retained);
    }
    {
        expr_ref symbolic_range(u.re.mk_range(s, s), m);
        expr_ref membership(u.re.mk_in_re(s, symbolic_range), m);
        expr_ref length(m.mk_eq(len, one), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, membership, nullptr, nullptr));
        state.add(dependent_expr(m, length, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == membership && state[1].fml() == length);
    }
    {
        expr_ref t(m.mk_const("regular-goal-t", u.str.mk_string_sort()), m);
        expr_ref t_first(u.str.mk_at(t, zero), m);
        goal_ref goal = alloc(::goal, m, false, false, false);
        goal->assert_expr(contains(prefix, "a"));
        goal->assert_expr(contains(t_first, "b"));
        tactic_ref tactic = alloc(dependent_expr_state_tactic, m, params_ref(),
            [](ast_manager& m, params_ref const& p, dependent_expr_state& state) -> dependent_expr_simplifier* {
                return alloc(seq_regular_simplifier, m, p, state);
            });
        goal_ref_buffer result;
        (*tactic)(goal, result);
        ENSURE(result.size() == 1 && result[0]->size() == 2);
        for (unsigned i = 0; i < result[0]->size(); ++i) {
            expr* root;
            expr* language;
            ENSURE(u.str.is_in_re(result[0]->form(i), root, language));
            ENSURE(root == s || root == t);
        }
    }
    struct {
        bool enabled;
        char const* solver;
        bool preprocess;
    } configurations[] = {{false, "nseq", true}, {true, "nseq", true}, {true, "seq", false}};
    for (auto const& config : configurations) {
        params_ref p;
        p.set_sym("string_solver", symbol(config.solver));
        p.set_bool("preprocess", config.preprocess);
        p.set_bool("seq.regular", config.enabled);
        smt_params params(p);
        asserted_formulas formulas(m, params, p);
        expr_ref no_a(m.mk_not(contains(prefix, "a")), m);
        expr_ref no_b(m.mk_not(contains(prefix, "b")), m);
        formulas.assert_expr(no_a);
        formulas.assert_expr(no_b);
        formulas.reduce();
        statistics st;
        formulas.collect_statistics(st);
        bool rewritten = false;
        for (unsigned i = 0; i < st.size(); ++i)
            rewritten |= std::strcmp(st.get_key(i), "seq-regular-rewritten") == 0;
        ENSURE(rewritten == config.enabled);
        if (config.enabled) {
            expr* root;
            expr* language;
            ENSURE(formulas.get_num_formulas() == 1);
            ENSURE(u.str.is_in_re(formulas.get_formula(0), root, language) && root == s);
        }

        solver_ref solver(mk_smt_solver(m, p, symbol()));
        solver->assert_expr(eq(s, "ab:"));
        ENSURE(solver->check_sat() == l_true);
        solver->push();
        solver->assert_expr(no_a);
        ENSURE(solver->check_sat() == l_false);
        solver->pop(1);
        ENSURE(solver->check_sat() == l_true);
    }
    {
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        smt_params params(p);
        asserted_formulas formulas(m, params, p);
        formulas.assert_expr(cases.get(0));
        p.set_bool("seq.regular", false);
        formulas.updt_params(p);
        formulas.reduce();
        statistics st;
        formulas.collect_statistics(st);
        ENSURE(st.size() == 0);
    }
    {
        solver_ref solver(mk_smt_solver(m, params_ref(), symbol()));
        solver->assert_expr(hold(a.mk_ge(len, integer(2))));
        ENSURE(solver->check_sat() == l_true);
        solver->assert_expr(hold(a.mk_gt(len, integer(2))));
        ENSURE(solver->check_sat() == l_true);
        statistics st;
        solver->collect_statistics(st);
        for (unsigned i = 0; i < st.size(); ++i)
            ENSURE(std::strcmp(st.get_key(i), "seq-regular-rewritten") != 0);
    }
    {
        base_dependent_expr_state state(m);
        expr_ref label(m.mk_const("regular-label", m.mk_bool_sort()), m);
        expr_dependency* dep = m.mk_leaf(label);
        state.add(dependent_expr(m, cases.get(0), nullptr, dep));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() != cases.get(0) && state[0].dep() == dep);
    }
    {
        base_dependent_expr_state state(m);
        sort* sorts[] = {u.str.mk_string_sort()};
        symbol names[] = {symbol("x")};
        expr_ref quantified(m.mk_forall(1, sorts, names, m.mk_true()), m);
        state.add(dependent_expr(m, cases.get(0), nullptr, nullptr));
        state.add(dependent_expr(m, quantified, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == cases.get(0) && state[1].fml() == quantified);
    }
    {
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        simplifier_factory factory = [](ast_manager& m, params_ref const& p, dependent_expr_state& state) {
            return alloc(seq_regular_simplifier, m, p, state);
        };
        solver_ref solver(mk_simplifier_solver(mk_smt_solver(m, p, symbol()), &factory));
        solver->assert_expr(eq(s, "a:"));
        ENSURE(solver->check_sat() == l_true);
        model_ref model;
        solver->get_model(model);
        expr_ref value(m);
        ENSURE(model.get() && model->eval(to_app(s)->get_decl(), value) && value == text("a:"));
        solver->push();
        solver->assert_expr(hold(m.mk_not(contains(s, "a"))));
        ENSURE(solver->check_sat() == l_false);
        solver->pop(1);
        ENSURE(solver->check_sat() == l_true);
        expr_ref assumption(eq(s, "b"), m);
        expr* assumptions[] = {assumption};
        ENSURE(solver->check_sat(1, assumptions) == l_false);
        ENSURE(solver->check_sat() == l_true);
        expr_ref label(m.mk_const("regular-conflict", m.mk_bool_sort()), m);
        solver->assert_expr(eq(s, "b"), label);
        ENSURE(solver->check_sat() == l_false);
        expr_ref_vector core(m);
        solver->get_unsat_core(core);
        ENSURE(core.size() == 1 && core.get(0) == label);
    }
    {
        base_dependent_expr_state state(m);
        expr_ref t(m.mk_const("regular-t", u.str.mk_string_sort()), m);
        expr_ref relational(m.mk_eq(s, t), m);
        state.add(dependent_expr(m, cases.get(0), nullptr, nullptr));
        state.add(dependent_expr(m, relational, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == cases.get(0) && state[1].fml() == relational);
    }
    {
        base_dependent_expr_state state(m);
        expr_ref t(m.mk_const("regular-ite-t", u.str.mk_string_sort()), m);
        expr_ref relational(m.mk_eq(s, t), m);
        expr_ref mixed(m.mk_ite(prefix_a, tail_b, relational), m);
        state.add(dependent_expr(m, mixed, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == mixed);
    }
    {
        expr_ref upper(a.mk_le(len, integer(8)), m);
        expr_ref shifted(a.mk_sub(len, integer(2)), m);
        expr_ref lower(a.mk_le(shifted, integer(7)), m);
        lower = m.mk_not(lower);
        expr_ref nested(m.mk_and(upper, m.mk_true()), m);
        expr_ref t(m.mk_const("regular-bound-t", u.str.mk_string_sort()), m);
        expr_ref relational(m.mk_eq(s, t), m);
        expr_ref hi_label(m.mk_const("regular-upper", m.mk_bool_sort()), m);
        expr_ref lo_label(m.mk_const("regular-lower", m.mk_bool_sort()), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, nested, nullptr, m.mk_leaf(hi_label)));
        state.add(dependent_expr(m, lower, nullptr, m.mk_leaf(lo_label)));
        state.add(dependent_expr(m, relational, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state.inconsistent() && m.is_false(state[0].fml()));
        ptr_vector<expr> premises;
        m.linearize(state[0].dep(), premises);
        ENSURE(premises.size() == 2 && premises.contains(hi_label) && premises.contains(lo_label));
    }
    for (bool guarded : {false, true}) {
        expr_ref upper(a.mk_le(len, integer(8)), m);
        expr_ref lower(a.mk_gt(len, integer(guarded ? 9 : 7)), m);
        if (guarded) {
            expr_ref boundary(m.mk_eq(len, integer(8)), m);
            lower = m.mk_or(lower, boundary);
        }
        expr_ref t(m.mk_const("regular-sat-bound-t", u.str.mk_string_sort()), m);
        expr_ref relational(m.mk_eq(s, t), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, upper, nullptr, nullptr));
        state.add(dependent_expr(m, lower, nullptr, nullptr));
        state.add(dependent_expr(m, relational, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(!state.inconsistent());
        ENSURE(state[0].fml() == upper && state[1].fml() == lower && state[2].fml() == relational);
    }
    for (int coefficient : {2, -2}) {
        expr_ref twice(a.mk_mul(integer(coefficient), len), m);
        expr_ref upper(a.mk_lt(twice, integer(coefficient > 0 ? 16 : -15)), m);
        expr_ref lower(a.mk_gt(twice, integer(coefficient > 0 ? 15 : -16)), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, upper, nullptr, nullptr));
        state.add(dependent_expr(m, lower, nullptr, nullptr));
        seq_regular_simplifier simp(m, params_ref(), state);
        simp.reduce();
        ENSURE(state.inconsistent());
    }
    {
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, cases.get(0), nullptr, nullptr));
        params_ref p;
        p.set_uint("seq_regular.max_steps", 1);
        seq_regular_simplifier simp(m, p, state);
        params_ref unrelated;
        unrelated.set_bool("model", true);
        simp.updt_params(unrelated);
        simp.reduce();
        ENSURE(state[0].fml() == cases.get(0));
    }
    {
        ast_manager proof_m(PGM_ENABLED);
        reg_decl_plugins(proof_m);
        seq_util proof_u(proof_m);
        expr_ref x(proof_m.mk_const("regular-proof-x", proof_u.str.mk_string_sort()), proof_m);
        expr_ref needle(proof_u.str.mk_string(zstring("a")), proof_m);
        expr_ref formula(proof_u.str.mk_contains(x, needle), proof_m);
        base_dependent_expr_state state(proof_m);
        state.add(dependent_expr(proof_m, formula, nullptr, nullptr));
        seq_regular_simplifier simp(proof_m, params_ref(), state);
        simp.reduce();
        ENSURE(state[0].fml() == formula);
    }
}

// max-bv-sharing must rewrite n-ary bvadd into binary trees that reuse
// common pairs. It does so without a preceding push: the operator kinds it
// handles are registered when it first rewrites a term.
static void test_max_bv_sharing() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_ast_vector assertions = Z3_parse_smtlib2_string(ctx,
        "(declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8))"
        "(declare-const c (_ BitVec 8)) (declare-const d (_ BitVec 8))"
        "(assert (distinct (bvadd a b c) (bvadd a b d)))",
        0, nullptr, nullptr, 0, nullptr, nullptr);
    Z3_ast_vector_inc_ref(ctx, assertions);
    Z3_goal goal = Z3_mk_goal(ctx, false, false, false);
    Z3_goal_inc_ref(ctx, goal);
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions); ++i)
        Z3_goal_assert(ctx, goal, Z3_ast_vector_get(ctx, assertions, i));
    Z3_tactic tactic = Z3_mk_tactic(ctx, "max-bv-sharing");
    Z3_tactic_inc_ref(ctx, tactic);
    Z3_apply_result result = Z3_tactic_apply(ctx, tactic, goal);
    Z3_apply_result_inc_ref(ctx, result);
    ENSURE(Z3_apply_result_get_num_subgoals(ctx, result) == 1);
    Z3_goal out = Z3_apply_result_get_subgoal(ctx, result, 0);
    ENSURE(Z3_goal_size(ctx, out) == 1);
    // Collect the distinct bvadd nodes of the result.
    std::vector<Z3_ast> todo{ Z3_goal_formula(ctx, out, 0) };
    std::vector<unsigned> adds;
    bool all_binary = true;
    while (!todo.empty()) {
        Z3_ast e = todo.back();
        todo.pop_back();
        if (Z3_get_ast_kind(ctx, e) != Z3_APP_AST)
            continue;
        Z3_app a = Z3_to_app(ctx, e);
        if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, a)) == Z3_OP_BADD) {
            unsigned id = Z3_get_ast_id(ctx, e);
            if (std::find(adds.begin(), adds.end(), id) != adds.end())
                continue;
            adds.push_back(id);
            all_binary &= Z3_get_app_num_args(ctx, a) == 2;
        }
        for (unsigned i = 0; i < Z3_get_app_num_args(ctx, a); ++i)
            todo.push_back(Z3_get_app_arg(ctx, a, i));
    }
    // (bvadd a b) is shared: (bvadd (bvadd a b) c), (bvadd (bvadd a b) d).
    ENSURE(all_binary);
    ENSURE(adds.size() == 3);
    Z3_apply_result_dec_ref(ctx, result);
    Z3_tactic_dec_ref(ctx, tactic);
    Z3_goal_dec_ref(ctx, goal);
    Z3_ast_vector_dec_ref(ctx, assertions);
    Z3_del_context(ctx);
}

void tst_simplifier() {

    test_asserted_formula_plugins();
    test_seq_regular_group_order();
    test_seq_decimal_comparisons();
    test_seq_bounded_conversions();
    test_seq_conversion_ranges();
    test_seq_regular_definitions();
    test_seq_regular();
    test_use_aware_replace_contains();
    test_proof_mode_simplifier_pipeline();
    test_bit2int_proofs();
    test_bit2int_zero_divisor_qe();
    test_nested_symbolic_rotations();
    test_quantified_bool_literals();
    test_array();
    test_const_array_lambda();
    test_bv();
    test_datatypes();
    test_bool();
    test_fpa();
    test_incremental_demodulator();
    test_recfun_finder();
    test_recfun_finder_guarded_body();
    test_solve_eqs_proofs();
    test_solve_eqs_macro_constants();
    test_solve_eqs_proof_scope();
    test_solve_eqs_max_occs();
    test_flatten_suffix_proofs();
    test_skolemize_bug();
    test_lambda_simplifier_proofs();
    test_pull_nested_quantifier_proofs();
    test_demodulator_simplifier_proofs();
    test_demodulator_quantified_proofs();
    test_max_bv_sharing();
}
