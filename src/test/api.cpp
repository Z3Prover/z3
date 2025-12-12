
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

void tst_api() {
    test_apps();
    test_bvneg();
    test_mk_distinct();
    test_optimize_translate();
}
