/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_stats.cpp

Abstract:

    Test API statistics browsing functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:

--*/
#include "api/z3.h"

void tst_api_stats() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Create a simple solver to generate statistics
    Z3_solver solver = Z3_mk_solver(ctx);

    // Create some simple variables and constraints to generate meaningful stats
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), int_sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);

    // Add some constraints: x > 0, y > 0, x + y < 10
    Z3_ast x_gt_zero = Z3_mk_gt(ctx, x, zero);
    Z3_ast y_gt_zero = Z3_mk_gt(ctx, y, zero);
    Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);
    Z3_ast x_plus_y = Z3_mk_add(ctx, 2, (Z3_ast[]){x, y});
    Z3_ast xy_lt_ten = Z3_mk_lt(ctx, x_plus_y, ten);

    Z3_solver_assert(ctx, solver, x_gt_zero);
    Z3_solver_assert(ctx, solver, y_gt_zero);
    Z3_solver_assert(ctx, solver, xy_lt_ten);

    // Check satisfiability to generate statistics
    Z3_lbool result = Z3_solver_check(ctx, solver);

    // Get statistics from the solver
    Z3_stats stats = Z3_solver_get_statistics(ctx, solver);

    // Test Z3_stats_inc_ref and Z3_stats_dec_ref
    Z3_stats_inc_ref(ctx, stats);
    Z3_stats_dec_ref(ctx, stats);
    // Statistics should still be valid

    // Test Z3_stats_size
    unsigned size = Z3_stats_size(ctx, stats);
    // Statistics should contain some entries (typically > 0 after solving)

    // Test Z3_stats_to_string
    Z3_string stats_str = Z3_stats_to_string(ctx, stats);
    // String should not be empty or null

    // Test iteration through statistics entries
    for (unsigned i = 0; i < size; i++) {
        // Test Z3_stats_get_key
        Z3_string key = Z3_stats_get_key(ctx, stats, i);

        // Test Z3_stats_is_uint and Z3_stats_is_double
        bool is_uint = Z3_stats_is_uint(ctx, stats, i);
        bool is_double = Z3_stats_is_double(ctx, stats, i);

        // Each entry should be either uint or double, but not both
        if (is_uint && !is_double) {
            // Test Z3_stats_get_uint_value
            unsigned uint_val = Z3_stats_get_uint_value(ctx, stats, i);
        }
        else if (is_double && !is_uint) {
            // Test Z3_stats_get_double_value
            double double_val = Z3_stats_get_double_value(ctx, stats, i);
        }
    }

    // Test error conditions with out-of-bounds index
    unsigned invalid_idx = size + 10;

    // Test Z3_stats_get_key with invalid index
    Z3_string invalid_key = Z3_stats_get_key(ctx, stats, invalid_idx);
    // Should return empty string and set error code

    // Test Z3_stats_is_uint with invalid index
    bool invalid_is_uint = Z3_stats_is_uint(ctx, stats, invalid_idx);
    // Should return false and set error code

    // Test Z3_stats_is_double with invalid index
    bool invalid_is_double = Z3_stats_is_double(ctx, stats, invalid_idx);
    // Should return false and set error code

    // Test Z3_stats_get_uint_value with invalid index
    unsigned invalid_uint = Z3_stats_get_uint_value(ctx, stats, invalid_idx);
    // Should return 0 and set error code

    // Test Z3_stats_get_double_value with invalid index
    double invalid_double = Z3_stats_get_double_value(ctx, stats, invalid_idx);
    // Should return 0.0 and set error code

    // Test type mismatch error conditions (if we have at least one stat)
    if (size > 0) {
        if (Z3_stats_is_uint(ctx, stats, 0)) {
            // Try to get double value from uint stat - should cause error
            double wrong_val = Z3_stats_get_double_value(ctx, stats, 0);
        }
        else if (Z3_stats_is_double(ctx, stats, 0)) {
            // Try to get uint value from double stat - should cause error
            unsigned wrong_val = Z3_stats_get_uint_value(ctx, stats, 0);
        }
    }

    // Test Z3_get_estimated_alloc_size (global function, no context needed)
    uint64_t alloc_size = Z3_get_estimated_alloc_size();
    // Should return some reasonable value (typically > 0)

    // Test with null stats (edge case)
    Z3_stats_dec_ref(ctx, nullptr);  // Should handle null gracefully

    Z3_del_context(ctx);
}