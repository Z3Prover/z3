/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_polynomial.cpp

Abstract:

    Test API polynomial functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"
#include <random>

static void run_single_test(int seed) {
    std::mt19937 gen(seed);
    std::uniform_int_distribution<> var_choice(0, 2);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort real_sort = Z3_mk_real_sort(ctx);

    // Create variables
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_symbol y_sym = Z3_mk_string_symbol(ctx, "y");
    Z3_symbol z_sym = Z3_mk_string_symbol(ctx, "z");
    Z3_ast x = Z3_mk_const(ctx, x_sym, real_sort);
    Z3_ast y = Z3_mk_const(ctx, y_sym, real_sort);
    Z3_ast z = Z3_mk_const(ctx, z_sym, real_sort);

    // Constants
    Z3_ast one = Z3_mk_real(ctx, 1, 1);
    Z3_ast two = Z3_mk_real(ctx, 2, 1);

    // Create polynomials: p = x + 1, q = x + 2
    Z3_ast add_args1[2] = {x, one};
    Z3_ast p = Z3_mk_add(ctx, 2, add_args1);
    Z3_ast add_args2[2] = {x, two};
    Z3_ast q = Z3_mk_add(ctx, 2, add_args2);

    // Choose which variable to use for subresultant
    Z3_ast var;
    int choice = var_choice(gen);
    switch (choice) {
        case 0: var = x; break;  // x is in the polynomials
        case 1: var = y; break;  // y is NOT in the polynomials
        default: var = z; break; // z is NOT in the polynomials
    }

    Z3_ast_vector result = Z3_polynomial_subresultants(ctx, p, q, var);
    ENSURE(result != nullptr);
    Z3_ast_vector_inc_ref(ctx, result);  // Take ownership
    unsigned size = Z3_ast_vector_size(ctx, result);
    // If var is x (in polynomials), expect 1 result; otherwise 0
    if (choice == 0) {
        ENSURE(size == 1);
    } else {
        ENSURE(size == 0);
    }
    Z3_ast_vector_dec_ref(ctx, result);  // Release ownership

    Z3_del_context(ctx);
}

void tst_api_polynomial() {
    // Run multiple tests with fresh contexts
    for (int i = 0; i < 20; i++) {
        run_single_test(i);
    }
}
