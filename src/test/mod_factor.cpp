/*++
Copyright (c) 2025 Microsoft Corporation
--*/

#include "api/z3.h"
#include "util/util.h"

// x mod 7 = 0 & (x*y) mod 7 != 0 should be unsat
// Exercises: mod internalization path (is_mod with numeric divisor)
static void test_mod_factor_mod_path() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), int_sort);
    Z3_ast seven = Z3_mk_int(ctx, 7, int_sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_mod(ctx, x, seven), zero));
    Z3_ast xy_args[] = {x, y};
    Z3_ast xy = Z3_mk_mul(ctx, 2, xy_args);
    Z3_solver_assert(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, Z3_mk_mod(ctx, xy, seven), zero)));
    ENSURE(Z3_solver_check(ctx, s) == Z3_L_FALSE);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

// (x mod 100) mod 7 = 0 => ((x mod 100) * y) mod 7 = 0
// Exercises: idiv internalization path (is_idiv + numeric divisor + bounded dividend)
// because (x mod 100) is recognized as bounded by is_bounded()
static void test_mod_factor_idiv_path() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), int_sort);
    Z3_ast seven = Z3_mk_int(ctx, 7, int_sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast hundred = Z3_mk_int(ctx, 100, int_sort);
    // xm = x mod 100 (bounded by is_bounded)
    Z3_ast xm = Z3_mk_mod(ctx, x, hundred);
    // xm mod 7 = 0
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_mod(ctx, xm, seven), zero));
    // (xm * y) div 7 — triggers idiv internalization with bounded dividend
    Z3_ast xm_y_args[] = {xm, y};
    Z3_ast xm_y = Z3_mk_mul(ctx, 2, xm_y_args);
    Z3_ast xm_y_div = Z3_mk_div(ctx, xm_y, seven);
    // assert (xm * y) mod 7 != 0
    Z3_solver_assert(ctx, s, Z3_mk_not(ctx, Z3_mk_eq(ctx, Z3_mk_mod(ctx, xm_y, seven), zero)));
    // use div to keep it alive
    Z3_solver_assert(ctx, s, Z3_mk_ge(ctx, xm_y_div, zero));
    ENSURE(Z3_solver_check(ctx, s) == Z3_L_FALSE);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void tst_mod_factor() {
    test_mod_factor_mod_path();
    test_mod_factor_idiv_path();
}
