
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
#include <thread>
#include <vector>

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

// Test for race condition in Z3_solver_translate when used in multiple threads
// Reproduces issue: https://github.com/prove-rs/z3.rs/issues/465
static void test_solver_translate_threading() {
    auto thread_fn = []() {
        Z3_config cfg = Z3_mk_config();
        Z3_context ctx1 = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        
        Z3_solver s = Z3_mk_solver(ctx1);
        Z3_solver_inc_ref(ctx1, s);
        
        // Create variables
        Z3_sort int_sort = Z3_mk_int_sort(ctx1);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx1, "x");
        Z3_symbol y_sym = Z3_mk_string_symbol(ctx1, "y");
        Z3_ast x = Z3_mk_const(ctx1, x_sym, int_sort);
        Z3_ast y = Z3_mk_const(ctx1, y_sym, int_sort);
        
        // Add constraints: y < 2
        Z3_ast two = Z3_mk_int(ctx1, 2, int_sort);
        Z3_ast y_lt_2 = Z3_mk_lt(ctx1, y, two);
        Z3_solver_assert(ctx1, s, y_lt_2);
        
        // Add constraints: x * y = -2
        Z3_ast neg_two = Z3_mk_int(ctx1, -2, int_sort);
        Z3_ast args[] = {x, y};
        Z3_ast mul = Z3_mk_mul(ctx1, 2, args);
        Z3_ast eq = Z3_mk_eq(ctx1, mul, neg_two);
        Z3_solver_assert(ctx1, s, eq);
        
        // Create new context and translate
        Z3_config cfg2 = Z3_mk_config();
        Z3_context ctx2 = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);
        
        Z3_solver s2 = Z3_solver_translate(ctx1, s, ctx2);
        Z3_solver_inc_ref(ctx2, s2);
        
        // Check satisfiability - should be SAT
        Z3_lbool result = Z3_solver_check(ctx2, s2);
        ENSURE(result == Z3_L_TRUE);
        
        // Cleanup
        Z3_solver_dec_ref(ctx2, s2);
        Z3_del_context(ctx2);
        Z3_solver_dec_ref(ctx1, s);
        Z3_del_context(ctx1);
    };
    
    std::vector<std::thread> threads;
    
    // Create multiple threads (more than typical CPU cores to trigger potential race)
    for (int i = 0; i < 20; ++i) {
        threads.emplace_back(thread_fn);
    }
    
    // Join all threads
    for (auto& t : threads) {
        t.join();
    }
}

void tst_api() {
    test_apps();
    test_bvneg();
    test_mk_distinct();
    test_solver_translate_threading();
}
