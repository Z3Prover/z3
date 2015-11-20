
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#ifdef _WINDOWS
#include "z3.h"
#include "z3_private.h"
#include <iostream>
#include "util.h"
#include "trace.h"
#include <map>
#include "trace.h"

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
    SASSERT(cb_called);
    Z3_del_config(cfg);
    Z3_del_context(ctx);    
    
}

void tst_api() {
    test_apps();
    test_bvneg();
    test_mk_distinct();
}
#else
void tst_api() {
}
#endif
