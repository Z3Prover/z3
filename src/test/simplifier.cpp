
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "api/z3.h"
#include "api/z3_private.h"
#include <cstring>
#include <iostream>
#include "util/util.h"
#include "util/trace.h"


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

void tst_simplifier() {

    test_array();
    test_bv();
    test_datatypes();
    test_bool();
    test_fpa();
    test_skolemize_bug();
}
