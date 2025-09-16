/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_algebraic.cpp

Abstract:

    Test API algebraic number functions

Author:

    Daily Test Coverage Improver 2025-09-16

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/rational.h"

void tst_api_algebraic() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Test Z3_algebraic_is_value with rational numbers
    {
        Z3_ast zero = Z3_mk_real(ctx, 0, 1);
        Z3_ast one = Z3_mk_real(ctx, 1, 1);
        Z3_ast negative_one = Z3_mk_real(ctx, -1, 1);
        Z3_ast half = Z3_mk_real(ctx, 1, 2);

        ENSURE(Z3_algebraic_is_value(ctx, zero));
        ENSURE(Z3_algebraic_is_value(ctx, one));
        ENSURE(Z3_algebraic_is_value(ctx, negative_one));
        ENSURE(Z3_algebraic_is_value(ctx, half));
    }

    // Test Z3_algebraic_is_value with non-algebraic values
    {
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
        Z3_sort real_sort = Z3_mk_real_sort(ctx);
        Z3_ast x = Z3_mk_const(ctx, x_sym, real_sort);

        // Variable should not be an algebraic value
        ENSURE(!Z3_algebraic_is_value(ctx, x));
    }

    // Test Z3_algebraic_is_zero, Z3_algebraic_is_pos, Z3_algebraic_is_neg
    {
        Z3_ast zero = Z3_mk_real(ctx, 0, 1);
        Z3_ast positive = Z3_mk_real(ctx, 5, 1);
        Z3_ast negative = Z3_mk_real(ctx, -3, 1);

        ENSURE(Z3_algebraic_is_zero(ctx, zero));
        ENSURE(!Z3_algebraic_is_pos(ctx, zero));
        ENSURE(!Z3_algebraic_is_neg(ctx, zero));

        ENSURE(!Z3_algebraic_is_zero(ctx, positive));
        ENSURE(Z3_algebraic_is_pos(ctx, positive));
        ENSURE(!Z3_algebraic_is_neg(ctx, positive));

        ENSURE(!Z3_algebraic_is_zero(ctx, negative));
        ENSURE(!Z3_algebraic_is_pos(ctx, negative));
        ENSURE(Z3_algebraic_is_neg(ctx, negative));
    }

    // Test Z3_algebraic_sign
    {
        Z3_ast zero = Z3_mk_real(ctx, 0, 1);
        Z3_ast positive = Z3_mk_real(ctx, 7, 1);
        Z3_ast negative = Z3_mk_real(ctx, -4, 1);

        ENSURE(Z3_algebraic_sign(ctx, zero) == 0);
        ENSURE(Z3_algebraic_sign(ctx, positive) > 0);
        ENSURE(Z3_algebraic_sign(ctx, negative) < 0);
    }

    // Test Z3_algebraic_add
    {
        Z3_ast two = Z3_mk_real(ctx, 2, 1);
        Z3_ast three = Z3_mk_real(ctx, 3, 1);
        Z3_ast five = Z3_mk_real(ctx, 5, 1);

        Z3_ast result = Z3_algebraic_add(ctx, two, three);
        ENSURE(Z3_algebraic_eq(ctx, result, five));
    }

    // Test Z3_algebraic_sub
    {
        Z3_ast seven = Z3_mk_real(ctx, 7, 1);
        Z3_ast three = Z3_mk_real(ctx, 3, 1);
        Z3_ast four = Z3_mk_real(ctx, 4, 1);

        Z3_ast result = Z3_algebraic_sub(ctx, seven, three);
        ENSURE(Z3_algebraic_eq(ctx, result, four));
    }

    // Test Z3_algebraic_mul
    {
        Z3_ast three = Z3_mk_real(ctx, 3, 1);
        Z3_ast four = Z3_mk_real(ctx, 4, 1);
        Z3_ast twelve = Z3_mk_real(ctx, 12, 1);

        Z3_ast result = Z3_algebraic_mul(ctx, three, four);
        ENSURE(Z3_algebraic_eq(ctx, result, twelve));
    }

    // Test Z3_algebraic_div
    {
        Z3_ast twelve = Z3_mk_real(ctx, 12, 1);
        Z3_ast three = Z3_mk_real(ctx, 3, 1);
        Z3_ast four = Z3_mk_real(ctx, 4, 1);

        Z3_ast result = Z3_algebraic_div(ctx, twelve, three);
        ENSURE(Z3_algebraic_eq(ctx, result, four));
    }

    // Test Z3_algebraic_power
    {
        Z3_ast two = Z3_mk_real(ctx, 2, 1);
        Z3_ast eight = Z3_mk_real(ctx, 8, 1);

        Z3_ast result = Z3_algebraic_power(ctx, two, 3);
        ENSURE(Z3_algebraic_eq(ctx, result, eight));
    }

    // Test comparison functions: Z3_algebraic_lt, Z3_algebraic_le, Z3_algebraic_gt, Z3_algebraic_ge
    {
        Z3_ast two = Z3_mk_real(ctx, 2, 1);
        Z3_ast three = Z3_mk_real(ctx, 3, 1);
        Z3_ast also_three = Z3_mk_real(ctx, 3, 1);

        // Less than
        ENSURE(Z3_algebraic_lt(ctx, two, three));
        ENSURE(!Z3_algebraic_lt(ctx, three, two));
        ENSURE(!Z3_algebraic_lt(ctx, three, also_three));

        // Less than or equal
        ENSURE(Z3_algebraic_le(ctx, two, three));
        ENSURE(!Z3_algebraic_le(ctx, three, two));
        ENSURE(Z3_algebraic_le(ctx, three, also_three));

        // Greater than
        ENSURE(!Z3_algebraic_gt(ctx, two, three));
        ENSURE(Z3_algebraic_gt(ctx, three, two));
        ENSURE(!Z3_algebraic_gt(ctx, three, also_three));

        // Greater than or equal
        ENSURE(!Z3_algebraic_ge(ctx, two, three));
        ENSURE(Z3_algebraic_ge(ctx, three, two));
        ENSURE(Z3_algebraic_ge(ctx, three, also_three));
    }

    // Test equality and inequality: Z3_algebraic_eq, Z3_algebraic_neq
    {
        Z3_ast two = Z3_mk_real(ctx, 2, 1);
        Z3_ast three = Z3_mk_real(ctx, 3, 1);
        Z3_ast also_two = Z3_mk_real(ctx, 2, 1);

        // Equality
        ENSURE(Z3_algebraic_eq(ctx, two, also_two));
        ENSURE(!Z3_algebraic_eq(ctx, two, three));

        // Inequality
        ENSURE(!Z3_algebraic_neq(ctx, two, also_two));
        ENSURE(Z3_algebraic_neq(ctx, two, three));
    }

    // Test Z3_algebraic_root
    {
        Z3_ast four = Z3_mk_real(ctx, 4, 1);
        Z3_ast two = Z3_mk_real(ctx, 2, 1);

        Z3_ast result = Z3_algebraic_root(ctx, four, 2); // Square root of 4
        ENSURE(Z3_algebraic_eq(ctx, result, two));
    }

    // Test with negative numbers and fractions
    {
        Z3_ast neg_half = Z3_mk_real(ctx, -1, 2);
        Z3_ast quarter = Z3_mk_real(ctx, 1, 4);
        Z3_ast neg_quarter = Z3_mk_real(ctx, -1, 4);

        ENSURE(Z3_algebraic_is_value(ctx, neg_half));
        ENSURE(Z3_algebraic_is_neg(ctx, neg_half));
        ENSURE(Z3_algebraic_is_pos(ctx, quarter));

        Z3_ast result = Z3_algebraic_add(ctx, neg_half, quarter);
        ENSURE(Z3_algebraic_eq(ctx, result, neg_quarter));
    }

    Z3_del_context(ctx);
}