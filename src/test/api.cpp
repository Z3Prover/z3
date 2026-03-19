
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "api/z3.h"
#include "api/z3_private.h"
#include <iostream>
#include "util/util.h"
#include "util/trace.h"
#include <map>
#include "util/trace.h"

void test_apps() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg,"MODEL","true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_symbol A = Z3_mk_string_symbol(ctx, "A");
    Z3_symbol F = Z3_mk_string_symbol(ctx, "f");
    Z3_sort SA = Z3_mk_uninterpreted_sort(ctx, A);
    Z3_func_decl f = Z3_mk_func_decl(ctx, F, 1, &SA, SA);
    Z3_symbol X = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, X, SA);
    Z3_ast fx = Z3_mk_app(ctx, f, 1, &x);
    Z3_ast ffx = Z3_mk_app(ctx, f, 1, &fx);
    Z3_ast fffx = Z3_mk_app(ctx, f, 1, &ffx);
    Z3_ast ffffx = Z3_mk_app(ctx, f, 1, &fffx);
    Z3_ast fffffx = Z3_mk_app(ctx, f, 1, &ffffx);

    Z3_ast fml = Z3_mk_not(ctx, Z3_mk_eq(ctx, x, fffffx));
    
    Z3_solver_assert(ctx, s, fml);
    Z3_lbool r = Z3_solver_check(ctx, s);
    std::cout << r << "\n";
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_bvneg() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg,"MODEL","true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    {
        Z3_sort bv30 = Z3_mk_bv_sort(ctx, 30);
        Z3_ast  x30 = Z3_mk_fresh_const(ctx, "x", bv30);
        Z3_ast fml = Z3_mk_eq(ctx, Z3_mk_int(ctx, -1, bv30), 
                              Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv30), 
                                      x30));        
        Z3_solver_assert(ctx, s, fml);
        Z3_lbool r = Z3_solver_check(ctx, s);
        std::cout << r << "\n";
    }

    {
        Z3_sort bv31 = Z3_mk_bv_sort(ctx, 31);
        Z3_ast  x31 = Z3_mk_fresh_const(ctx, "x", bv31);
        Z3_ast fml = Z3_mk_eq(ctx, Z3_mk_int(ctx, -1, bv31), 
                              Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv31), 
                                      x31));        
        Z3_solver_assert(ctx, s, fml);
        Z3_lbool r = Z3_solver_check(ctx, s);
        std::cout << r << "\n";
    }

    {
        Z3_sort bv32 = Z3_mk_bv_sort(ctx, 32);
        Z3_ast  x32 = Z3_mk_fresh_const(ctx, "x", bv32);
        Z3_ast fml = Z3_mk_eq(ctx, 
                              Z3_mk_int(ctx,-1, bv32), 
                              Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv32), 
                                          x32));        
        Z3_solver_assert(ctx, s, fml);
        Z3_lbool r = Z3_solver_check(ctx, s);
        std::cout << r << "\n";
    }

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);    
}

static bool cb_called = false;
static void my_cb(Z3_context, Z3_error_code) {
    cb_called = true;
}

static void test_mk_distinct() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, my_cb);
    
    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_sort bv32 = Z3_mk_bv_sort(ctx, 32);
    Z3_ast args[] = { Z3_mk_int64(ctx, 0, bv8), Z3_mk_int64(ctx, 0, bv32) };
    Z3_ast d = Z3_mk_distinct(ctx, 2, args);
    ENSURE(cb_called);
    VERIFY(!d);
    Z3_del_config(cfg);
    Z3_del_context(ctx);    
    
}

void test_optimize_translate() {
    Z3_config cfg1 = Z3_mk_config();
    Z3_context ctx1 = Z3_mk_context(cfg1);
    Z3_del_config(cfg1);
    
    // Create optimization context in first context
    Z3_optimize opt1 = Z3_mk_optimize(ctx1);
    Z3_optimize_inc_ref(ctx1, opt1);
    
    // Add some constraints
    Z3_sort int_sort = Z3_mk_int_sort(ctx1);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx1, "x");
    Z3_ast x = Z3_mk_const(ctx1, x_sym, int_sort);
    
    Z3_ast zero = Z3_mk_int(ctx1, 0, int_sort);
    Z3_ast constraint = Z3_mk_gt(ctx1, x, zero);  // x > 0
    
    Z3_optimize_assert(ctx1, opt1, constraint);
    
    // Add an objective to maximize x
    Z3_optimize_maximize(ctx1, opt1, x);
    
    // Create second context
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);
    
    // Translate optimize context to second context
    Z3_optimize opt2 = Z3_optimize_translate(ctx1, opt1, ctx2);
    Z3_optimize_inc_ref(ctx2, opt2);
    
    // Check sat in the translated context
    Z3_lbool result = Z3_optimize_check(ctx2, opt2, 0, nullptr);
    
    ENSURE(result == Z3_L_TRUE);
    
    // Verify we can get assertions from translated context
    Z3_ast_vector assertions = Z3_optimize_get_assertions(ctx2, opt2);
    unsigned num_assertions = Z3_ast_vector_size(ctx2, assertions);
    ENSURE(num_assertions == 1);
    
    // Verify we can get objectives from translated context
    Z3_ast_vector objectives = Z3_optimize_get_objectives(ctx2, opt2);
    unsigned num_objectives = Z3_ast_vector_size(ctx2, objectives);
    ENSURE(num_objectives == 1);
    
    // Clean up
    Z3_optimize_dec_ref(ctx2, opt2);
    Z3_optimize_dec_ref(ctx1, opt1);
    Z3_del_context(ctx2);
    Z3_del_context(ctx1);
}

void test_max_reg() {    
    // BNH multi-objective optimization problem using Z3 Optimize C API.
    // Mimics /tmp/bnh_z3.py: two objectives over a constrained 2D domain.
    //   f1 = 4*x1^2 + 4*x2^2
    //   f2 = (x1-5)^2 + (x2-5)^2
    //   0 <= x1 <= 5, 0 <= x2 <= 3
    //   C1: (x1-5)^2 + x2^2 <= 25
    //   C2: (x1-8)^2 + (x2+3)^2 >= 7.7

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort real_sort = Z3_mk_real_sort(ctx);
    Z3_ast x1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x1"), real_sort);
    Z3_ast x2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x2"), real_sort);

    auto mk_real = [&](int num, int den = 1) { return Z3_mk_real(ctx, num, den); };
    auto mk_mul = [&](Z3_ast a, Z3_ast b) { Z3_ast args[] = {a, b}; return Z3_mk_mul(ctx, 2, args); };
    auto mk_add = [&](Z3_ast a, Z3_ast b) { Z3_ast args[] = {a, b}; return Z3_mk_add(ctx, 2, args); };
    auto mk_sub = [&](Z3_ast a, Z3_ast b) { Z3_ast args[] = {a, b}; return Z3_mk_sub(ctx, 2, args); };
    auto mk_sq = [&](Z3_ast a) { return mk_mul(a, a); };

    // f1 = 4*x1^2 + 4*x2^2
    Z3_ast f1 = mk_add(mk_mul(mk_real(4), mk_sq(x1)), mk_mul(mk_real(4), mk_sq(x2)));
    // f2 = (x1-5)^2 + (x2-5)^2
    Z3_ast f2 = mk_add(mk_sq(mk_sub(x1, mk_real(5))), mk_sq(mk_sub(x2, mk_real(5))));

    // Helper: create optimize with BNH constraints and timeout
    auto mk_max_reg = [&]() -> Z3_optimize {
        Z3_optimize opt = Z3_mk_optimize(ctx);
        Z3_optimize_inc_ref(ctx, opt);
        // Set timeout to 5 seconds
        Z3_params p = Z3_mk_params(ctx);
        Z3_params_inc_ref(ctx, p);
        Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), 5000);
        Z3_optimize_set_params(ctx, opt, p);
        Z3_params_dec_ref(ctx, p);
        // Add BNH constraints
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x1, mk_real(0)));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x1, mk_real(5)));
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x2, mk_real(0)));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x2, mk_real(3)));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, mk_add(mk_sq(mk_sub(x1, mk_real(5))), mk_sq(x2)), mk_real(25)));
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, mk_add(mk_sq(mk_sub(x1, mk_real(8))), mk_sq(mk_add(x2, mk_real(3)))), mk_real(77, 10)));
        return opt;
    };

    auto result_str = [](Z3_lbool r) { return r == Z3_L_TRUE ? "sat" : r == Z3_L_FALSE ? "unsat" : "unknown"; };

    unsigned num_sat = 0;

    // Approach 1: Minimize f1 (Python: opt.minimize(f1))
    {
        Z3_optimize opt = mk_max_reg();
        Z3_optimize_minimize(ctx, opt, f1);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << "BNH min f1: " << result_str(result) << std::endl;
        ENSURE(result == Z3_L_TRUE);
        if (result == Z3_L_TRUE) {
            Z3_model m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            Z3_ast val; Z3_model_eval(ctx, m, f1, true, &val);
            std::cout << "  f1=" << Z3_ast_to_string(ctx, val) << std::endl;
            Z3_model_dec_ref(ctx, m);
            num_sat++;
        }
        Z3_optimize_dec_ref(ctx, opt);
    }

    // Approach 2: Minimize f2 (Python: opt2.minimize(f2))
    {
        Z3_optimize opt = mk_max_reg();
        Z3_optimize_minimize(ctx, opt, f2);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << "BNH min f2: " << result_str(result) << std::endl;
        ENSURE(result == Z3_L_TRUE);
        if (result == Z3_L_TRUE) {
            Z3_model m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            Z3_ast val; Z3_model_eval(ctx, m, f2, true, &val);
            std::cout << "  f2=" << Z3_ast_to_string(ctx, val) << std::endl;
            Z3_model_dec_ref(ctx, m);
            num_sat++;
        }
        Z3_optimize_dec_ref(ctx, opt);
    }

    // Approach 3: Weighted sum method (Python loop over weights)
    int weights[][2] = {{1, 4}, {2, 3}, {1, 1}, {3, 2}, {4, 1}};
    for (auto& w : weights) {
        Z3_optimize opt = mk_max_reg();
        Z3_ast weighted = mk_add(mk_mul(mk_real(w[0], 100), f1), mk_mul(mk_real(w[1], 100), f2));
        Z3_optimize_minimize(ctx, opt, weighted);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << "BNH weighted (w1=" << w[0] << "/5, w2=" << w[1] << "/5): "
                  << result_str(result) << std::endl;
        ENSURE(result == Z3_L_TRUE);
        if (result == Z3_L_TRUE) {
            Z3_model m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            Z3_ast v1, v2;
            Z3_model_eval(ctx, m, f1, true, &v1);
            Z3_model_eval(ctx, m, f2, true, &v2);
            std::cout << "  f1=" << Z3_ast_to_string(ctx, v1)
                      << " f2=" << Z3_ast_to_string(ctx, v2) << std::endl;
            Z3_model_dec_ref(ctx, m);
            num_sat++;
        }
        Z3_optimize_dec_ref(ctx, opt);
    }

    std::cout << "BNH: " << num_sat << "/7 optimizations returned sat" << std::endl;
    ENSURE(num_sat == 7);
    Z3_del_context(ctx);
    std::cout << "BNH optimization test done" << std::endl;
}

void tst_api() {
    test_apps();
    test_bvneg();
    test_mk_distinct();
    test_optimize_translate();
}

void tst_max_reg() {
    test_max_reg();
}

void test_max_rev() {
    // Same as test_max_regimize but with reversed argument order in f1/f2 construction.
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort real_sort = Z3_mk_real_sort(ctx);
    Z3_ast x1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x1"), real_sort);
    Z3_ast x2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x2"), real_sort);

    auto mk_real = [&](int num, int den = 1) { return Z3_mk_real(ctx, num, den); };
    auto mk_mul = [&](Z3_ast a, Z3_ast b) { Z3_ast args[] = {a, b}; return Z3_mk_mul(ctx, 2, args); };
    auto mk_add = [&](Z3_ast a, Z3_ast b) { Z3_ast args[] = {a, b}; return Z3_mk_add(ctx, 2, args); };
    auto mk_sub = [&](Z3_ast a, Z3_ast b) { Z3_ast args[] = {a, b}; return Z3_mk_sub(ctx, 2, args); };
    auto mk_sq = [&](Z3_ast a) { return mk_mul(a, a); };

    // f1 = 4*x2^2 + 4*x1^2  (reversed from: 4*x1^2 + 4*x2^2)
    Z3_ast f1 = mk_add(mk_mul(mk_sq(x2), mk_real(4)), mk_mul(mk_sq(x1), mk_real(4)));
    // f2 = (x2-5)^2 + (x1-5)^2  (reversed from: (x1-5)^2 + (x2-5)^2)
    Z3_ast f2 = mk_add(mk_sq(mk_sub(mk_real(5), x2)), mk_sq(mk_sub(mk_real(5), x1)));

    auto mk_max_reg = [&]() -> Z3_optimize {
        Z3_optimize opt = Z3_mk_optimize(ctx);
        Z3_optimize_inc_ref(ctx, opt);
        Z3_params p = Z3_mk_params(ctx);
        Z3_params_inc_ref(ctx, p);
        Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), 5000);
        Z3_optimize_set_params(ctx, opt, p);
        Z3_params_dec_ref(ctx, p);
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x1, mk_real(0)));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x1, mk_real(5)));
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, x2, mk_real(0)));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, x2, mk_real(3)));
        Z3_optimize_assert(ctx, opt, Z3_mk_le(ctx, mk_add(mk_sq(mk_sub(mk_real(5), x1)), mk_sq(x2)), mk_real(25)));
        Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, mk_add(mk_sq(mk_sub(mk_real(8), x1)), mk_sq(mk_add(mk_real(3), x2))), mk_real(77, 10)));
        return opt;
    };

    auto result_str = [](Z3_lbool r) { return r == Z3_L_TRUE ? "sat" : r == Z3_L_FALSE ? "unsat" : "unknown"; };

    unsigned num_sat = 0;

    {
        Z3_optimize opt = mk_max_reg();
        Z3_optimize_minimize(ctx, opt, f1);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << "max_rev min f1: " << result_str(result) << std::endl;
        ENSURE(result == Z3_L_TRUE);
        if (result == Z3_L_TRUE) {
            Z3_model m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            Z3_ast val; Z3_model_eval(ctx, m, f1, true, &val);
            std::cout << "  f1=" << Z3_ast_to_string(ctx, val) << std::endl;
            Z3_model_dec_ref(ctx, m);
            num_sat++;
        }
        Z3_optimize_dec_ref(ctx, opt);
    }

    {
        Z3_optimize opt = mk_max_reg();
        Z3_optimize_minimize(ctx, opt, f2);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << "max_rev min f2: " << result_str(result) << std::endl;
        ENSURE(result == Z3_L_TRUE);
        if (result == Z3_L_TRUE) {
            Z3_model m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            Z3_ast val; Z3_model_eval(ctx, m, f2, true, &val);
            std::cout << "  f2=" << Z3_ast_to_string(ctx, val) << std::endl;
            Z3_model_dec_ref(ctx, m);
            num_sat++;
        }
        Z3_optimize_dec_ref(ctx, opt);
    }

    int weights[][2] = {{1, 4}, {2, 3}, {1, 1}, {3, 2}, {4, 1}};
    for (auto& w : weights) {
        Z3_optimize opt = mk_max_reg();
        Z3_ast weighted = mk_add(mk_mul(mk_real(w[1], 100), f2), mk_mul(mk_real(w[0], 100), f1));
        Z3_optimize_minimize(ctx, opt, weighted);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << "max_rev weighted (w1=" << w[0] << "/5, w2=" << w[1] << "/5): "
                  << result_str(result) << std::endl;
        ENSURE(result == Z3_L_TRUE);
        if (result == Z3_L_TRUE) {
            Z3_model m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            Z3_ast v1, v2;
            Z3_model_eval(ctx, m, f1, true, &v1);
            Z3_model_eval(ctx, m, f2, true, &v2);
            std::cout << "  f1=" << Z3_ast_to_string(ctx, v1)
                      << " f2=" << Z3_ast_to_string(ctx, v2) << std::endl;
            Z3_model_dec_ref(ctx, m);
            num_sat++;
        }
        Z3_optimize_dec_ref(ctx, opt);
    }

    std::cout << "max_rev: " << num_sat << "/7 optimizations returned sat" << std::endl;
    ENSURE(num_sat == 7);
    Z3_del_context(ctx);
    std::cout << "max_rev optimization test done" << std::endl;
}

// Regression test for issue #8998:
// minimize(3*a) should be unbounded, same as minimize(a),
// when constraints allow a to go to -infinity.
void test_scaled_minimize_unbounded() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort real_sort = Z3_mk_real_sort(ctx);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), real_sort);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), real_sort);

    // (xor (= 0 b) (> (mod (to_int (- a)) 50) 3))
    Z3_ast neg_a = Z3_mk_unary_minus(ctx, a);
    Z3_ast to_int_neg_a = Z3_mk_real2int(ctx, neg_a);
    Z3_ast mod_expr = Z3_mk_mod(ctx, to_int_neg_a, Z3_mk_int(ctx, 50, int_sort));
    Z3_ast gt_3 = Z3_mk_gt(ctx, mod_expr, Z3_mk_int(ctx, 3, int_sort));
    Z3_ast b_eq_0 = Z3_mk_eq(ctx, Z3_mk_real(ctx, 0, 1), b);
    Z3_ast xor_expr = Z3_mk_xor(ctx, b_eq_0, gt_3);

    auto check_unbounded_min = [&](Z3_ast objective, const char* label) {
        Z3_optimize opt = Z3_mk_optimize(ctx);
        Z3_optimize_inc_ref(ctx, opt);
        Z3_optimize_assert(ctx, opt, xor_expr);
        unsigned h = Z3_optimize_minimize(ctx, opt, objective);
        Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
        std::cout << label << ": " << (result == Z3_L_TRUE ? "sat" : "not sat") << std::endl;
        ENSURE(result == Z3_L_TRUE);
        // get_lower_as_vector returns [infinity_coeff, rational, epsilon_coeff]
        // for -infinity, infinity_coeff should be negative
        Z3_ast_vector lower = Z3_optimize_get_lower_as_vector(ctx, opt, h);
        Z3_ast inf_coeff = Z3_ast_vector_get(ctx, lower, 0);
        int64_t inf_val;
        bool ok = Z3_get_numeral_int64(ctx, inf_coeff, &inf_val);
        std::cout << "  infinity coeff: " << inf_val << std::endl;
        ENSURE(ok && inf_val < 0);
        Z3_optimize_dec_ref(ctx, opt);
    };

    // minimize(a) should be -infinity
    check_unbounded_min(a, "minimize(a)");

    // minimize(3*a) should also be -infinity
    Z3_ast three = Z3_mk_real(ctx, 3, 1);
    Z3_ast args[] = {three, a};
    Z3_ast three_a = Z3_mk_mul(ctx, 2, args);
    check_unbounded_min(three_a, "minimize(3*a)");

    Z3_del_context(ctx);
    std::cout << "scaled minimize unbounded test done" << std::endl;
}

void tst_scaled_min() {
    test_scaled_minimize_unbounded();
}

void tst_max_rev() {
    test_max_rev();
}

// Regression test for issue #9012: box mode returns wrong optimum for mod.
// With (set-option :opt.priority box) and multiple objectives,
// maximize (mod (- (* 232 a)) 256) must return 248, not 0.
void tst_box_mod_opt() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), int_sort);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), int_sort);
    Z3_ast d = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "d"), int_sort);
    Z3_ast c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "c"), int_sort);

    auto mk_int = [&](int v) { return Z3_mk_int(ctx, v, int_sort); };
    auto mk_int64 = [&](int64_t v) { return Z3_mk_int64(ctx, v, int_sort); };

    Z3_optimize opt = Z3_mk_optimize(ctx);
    Z3_optimize_inc_ref(ctx, opt);

    // set box priority
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_symbol(ctx, p, Z3_mk_string_symbol(ctx, "priority"),
                         Z3_mk_string_symbol(ctx, "box"));
    Z3_optimize_set_params(ctx, opt, p);
    Z3_params_dec_ref(ctx, p);

    // bounds: 0 <= a < 256, 0 <= b < 2^32, 0 <= d < 2^32, 0 <= c < 16
    Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, a, mk_int(0)));
    Z3_optimize_assert(ctx, opt, Z3_mk_lt(ctx, a, mk_int(256)));
    Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, b, mk_int(0)));
    Z3_optimize_assert(ctx, opt, Z3_mk_lt(ctx, b, mk_int64(4294967296)));
    Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, d, mk_int(0)));
    Z3_optimize_assert(ctx, opt, Z3_mk_lt(ctx, d, mk_int64(4294967296)));
    Z3_optimize_assert(ctx, opt, Z3_mk_ge(ctx, c, mk_int(0)));
    Z3_optimize_assert(ctx, opt, Z3_mk_lt(ctx, c, mk_int(16)));

    // minimize (mod (* d 536144634) 4294967296)
    Z3_ast mul_d_args[] = { mk_int64(536144634), d };
    Z3_ast mul_d = Z3_mk_mul(ctx, 2, mul_d_args);
    Z3_optimize_minimize(ctx, opt, Z3_mk_mod(ctx, mul_d, mk_int64(4294967296)));

    // minimize b
    Z3_optimize_minimize(ctx, opt, b);

    // maximize (mod (- (* 232 a)) 256)
    Z3_ast mul_a_args[] = { mk_int(232), a };
    Z3_ast mul_a = Z3_mk_mul(ctx, 2, mul_a_args);
    Z3_ast neg_mul_a = Z3_mk_unary_minus(ctx, mul_a);
    unsigned max_idx = Z3_optimize_maximize(ctx, opt, Z3_mk_mod(ctx, neg_mul_a, mk_int(256)));

    Z3_lbool result = Z3_optimize_check(ctx, opt, 0, nullptr);
    ENSURE(result == Z3_L_TRUE);

    // The optimum of (mod (- (* 232 a)) 256) should be 248
    Z3_ast lower = Z3_optimize_get_lower(ctx, opt, max_idx);
    Z3_string lower_str = Z3_ast_to_string(ctx, lower);
    ENSURE(std::string(lower_str) == "248");

    Z3_optimize_dec_ref(ctx, opt);
    Z3_del_context(ctx);
    std::cout << "box mod optimization test passed" << std::endl;
}
