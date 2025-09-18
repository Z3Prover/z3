/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_pb.cpp

Abstract:

    Test API pseudo-boolean constraint functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:
    Tests the Z3 API functions for creating pseudo-boolean constraints:
    - Z3_mk_atmost: at most k of the variables can be true
    - Z3_mk_atleast: at least k of the variables can be true
    - Z3_mk_pble: weighted pseudo-boolean less-than-or-equal constraint
    - Z3_mk_pbge: weighted pseudo-boolean greater-than-or-equal constraint
    - Z3_mk_pbeq: weighted pseudo-boolean equality constraint

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"

void tst_api_pb() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Create some boolean variables for testing
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), bool_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), bool_sort);
    Z3_ast z = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "z"), bool_sort);

    // Test Z3_mk_atmost: at most k variables can be true
    {
        Z3_ast vars[] = {x, y, z};
        Z3_ast constraint = Z3_mk_atmost(ctx, 3, vars, 2);
        ENSURE(constraint != nullptr);

        // Test with zero variables (edge case)
        Z3_ast constraint_empty = Z3_mk_atmost(ctx, 0, nullptr, 0);
        ENSURE(constraint_empty != nullptr);

        // Test with single variable
        Z3_ast constraint_single = Z3_mk_atmost(ctx, 1, vars, 1);
        ENSURE(constraint_single != nullptr);
    }

    // Test Z3_mk_atleast: at least k variables can be true
    {
        Z3_ast vars[] = {x, y, z};
        Z3_ast constraint = Z3_mk_atleast(ctx, 3, vars, 1);
        ENSURE(constraint != nullptr);

        // Test with zero threshold
        Z3_ast constraint_zero = Z3_mk_atleast(ctx, 3, vars, 0);
        ENSURE(constraint_zero != nullptr);

        // Test with all variables required
        Z3_ast constraint_all = Z3_mk_atleast(ctx, 3, vars, 3);
        ENSURE(constraint_all != nullptr);
    }

    // Test Z3_mk_pble: weighted pseudo-boolean less-than-or-equal
    {
        Z3_ast vars[] = {x, y, z};
        int coeffs[] = {1, 2, 3}; // weights for x, y, z
        Z3_ast constraint = Z3_mk_pble(ctx, 3, vars, coeffs, 4);
        ENSURE(constraint != nullptr);

        // Test with negative coefficients
        int neg_coeffs[] = {-1, 2, -3};
        Z3_ast constraint_neg = Z3_mk_pble(ctx, 3, vars, neg_coeffs, 0);
        ENSURE(constraint_neg != nullptr);

        // Test with zero coefficients
        int zero_coeffs[] = {0, 0, 0};
        Z3_ast constraint_zero = Z3_mk_pble(ctx, 3, vars, zero_coeffs, 5);
        ENSURE(constraint_zero != nullptr);

        // Test with single variable
        int single_coeff[] = {5};
        Z3_ast constraint_single = Z3_mk_pble(ctx, 1, vars, single_coeff, 3);
        ENSURE(constraint_single != nullptr);
    }

    // Test Z3_mk_pbge: weighted pseudo-boolean greater-than-or-equal
    {
        Z3_ast vars[] = {x, y, z};
        int coeffs[] = {2, 3, 1}; // weights for x, y, z
        Z3_ast constraint = Z3_mk_pbge(ctx, 3, vars, coeffs, 3);
        ENSURE(constraint != nullptr);

        // Test with large coefficients
        int large_coeffs[] = {100, 200, 50};
        Z3_ast constraint_large = Z3_mk_pbge(ctx, 3, vars, large_coeffs, 150);
        ENSURE(constraint_large != nullptr);

        // Test with negative threshold
        int pos_coeffs[] = {1, 1, 1};
        Z3_ast constraint_neg_threshold = Z3_mk_pbge(ctx, 3, vars, pos_coeffs, -1);
        ENSURE(constraint_neg_threshold != nullptr);
    }

    // Test Z3_mk_pbeq: weighted pseudo-boolean equality
    {
        Z3_ast vars[] = {x, y, z};
        int coeffs[] = {1, 1, 1}; // equal weights
        Z3_ast constraint = Z3_mk_pbeq(ctx, 3, vars, coeffs, 2);
        ENSURE(constraint != nullptr);

        // Test with different coefficients
        int diff_coeffs[] = {3, 5, 7};
        Z3_ast constraint_diff = Z3_mk_pbeq(ctx, 3, vars, diff_coeffs, 5);
        ENSURE(constraint_diff != nullptr);

        // Test with zero threshold
        int unit_coeffs[] = {2, 4, 6};
        Z3_ast constraint_zero_eq = Z3_mk_pbeq(ctx, 3, vars, unit_coeffs, 0);
        ENSURE(constraint_zero_eq != nullptr);
    }

    // Test complex scenario: combining different constraints
    {
        Z3_ast vars[] = {x, y, z};
        int coeffs[] = {1, 2, 3};

        Z3_ast atmost_constraint = Z3_mk_atmost(ctx, 3, vars, 2);
        Z3_ast atleast_constraint = Z3_mk_atleast(ctx, 3, vars, 1);
        Z3_ast pble_constraint = Z3_mk_pble(ctx, 3, vars, coeffs, 5);
        Z3_ast pbge_constraint = Z3_mk_pbge(ctx, 3, vars, coeffs, 2);
        Z3_ast pbeq_constraint = Z3_mk_pbeq(ctx, 3, vars, coeffs, 3);

        ENSURE(atmost_constraint != nullptr);
        ENSURE(atleast_constraint != nullptr);
        ENSURE(pble_constraint != nullptr);
        ENSURE(pbge_constraint != nullptr);
        ENSURE(pbeq_constraint != nullptr);

        // Create a conjunction of constraints to ensure they can be combined
        Z3_ast constraints[] = {atmost_constraint, atleast_constraint};
        Z3_ast combined = Z3_mk_and(ctx, 2, constraints);
        ENSURE(combined != nullptr);
    }

    // Test edge cases with empty arrays
    {
        // Empty array should work for atmost/atleast
        Z3_ast empty_atmost = Z3_mk_atmost(ctx, 0, nullptr, 0);
        Z3_ast empty_atleast = Z3_mk_atleast(ctx, 0, nullptr, 0);
        ENSURE(empty_atmost != nullptr);
        ENSURE(empty_atleast != nullptr);

        // Empty arrays should work for weighted constraints too
        Z3_ast empty_pble = Z3_mk_pble(ctx, 0, nullptr, nullptr, 5);
        Z3_ast empty_pbge = Z3_mk_pbge(ctx, 0, nullptr, nullptr, -2);
        Z3_ast empty_pbeq = Z3_mk_pbeq(ctx, 0, nullptr, nullptr, 0);
        ENSURE(empty_pble != nullptr);
        ENSURE(empty_pbge != nullptr);
        ENSURE(empty_pbeq != nullptr);
    }

    Z3_del_context(ctx);
}