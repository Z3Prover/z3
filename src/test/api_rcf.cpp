/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    api_rcf.cpp

Abstract:

    Tests for Z3 real closed field (RCF) API functions

Author:

    Daily Test Coverage Improver 2025-09-17

--*/
#include "z3.h"
#include <iostream>
#include <cassert>
#include <cstring>

void tst_api_rcf() {
    std::cout << "testing RCF API...\n";

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Test basic RCF number creation
    Z3_rcf_num zero = Z3_rcf_mk_small_int(ctx, 0);
    Z3_rcf_num one = Z3_rcf_mk_small_int(ctx, 1);
    Z3_rcf_num two = Z3_rcf_mk_small_int(ctx, 2);
    Z3_rcf_num neg_one = Z3_rcf_mk_small_int(ctx, -1);

    // Test rational number creation
    Z3_rcf_num half = Z3_rcf_mk_rational(ctx, "1/2");
    Z3_rcf_num quarter = Z3_rcf_mk_rational(ctx, "1/4");
    Z3_rcf_num three_halves = Z3_rcf_mk_rational(ctx, "3/2");

    // Test transcendental constants
    Z3_rcf_num pi = Z3_rcf_mk_pi(ctx);
    Z3_rcf_num e = Z3_rcf_mk_e(ctx);

    // Test infinitesimal
    Z3_rcf_num inf_small = Z3_rcf_mk_infinitesimal(ctx);

    // Test arithmetic operations
    Z3_rcf_num sum = Z3_rcf_add(ctx, one, two);     // 1 + 2 = 3
    Z3_rcf_num diff = Z3_rcf_sub(ctx, two, one);    // 2 - 1 = 1
    Z3_rcf_num prod = Z3_rcf_mul(ctx, two, half);   // 2 * (1/2) = 1
    Z3_rcf_num quot = Z3_rcf_div(ctx, one, two);    // 1 / 2 = 1/2
    Z3_rcf_num neg = Z3_rcf_neg(ctx, one);          // -1
    Z3_rcf_num inv = Z3_rcf_inv(ctx, two);          // 1/2
    Z3_rcf_num pow2 = Z3_rcf_power(ctx, two, 2);    // 2^2 = 4
    Z3_rcf_num pow3 = Z3_rcf_power(ctx, two, 3);    // 2^3 = 8

    // Test all comparison operations
    assert(Z3_rcf_lt(ctx, one, two));          // 1 < 2
    assert(!Z3_rcf_lt(ctx, two, one));         // not 2 < 1
    assert(Z3_rcf_gt(ctx, two, one));          // 2 > 1
    assert(!Z3_rcf_gt(ctx, one, two));         // not 1 > 2
    assert(Z3_rcf_le(ctx, one, one));          // 1 <= 1
    assert(Z3_rcf_le(ctx, one, two));          // 1 <= 2
    assert(Z3_rcf_ge(ctx, one, one));          // 1 >= 1
    assert(Z3_rcf_ge(ctx, two, one));          // 2 >= 1
    assert(Z3_rcf_eq(ctx, one, one));          // 1 == 1
    assert(!Z3_rcf_eq(ctx, one, two));         // not 1 == 2
    assert(Z3_rcf_neq(ctx, one, two));         // 1 != 2
    assert(!Z3_rcf_neq(ctx, one, one));        // not 1 != 1

    // Test negative number comparisons
    assert(Z3_rcf_lt(ctx, neg_one, zero));     // -1 < 0
    assert(Z3_rcf_gt(ctx, zero, neg_one));     // 0 > -1

    // Test transcendental comparisons
    assert(Z3_rcf_gt(ctx, pi, two));           // π > 2
    assert(Z3_rcf_gt(ctx, pi, e));             // π > e (π ≈ 3.14, e ≈ 2.72)

    // Test infinitesimal comparisons (just test that they don't crash)
    Z3_rcf_lt(ctx, inf_small, zero);   // Test infinitesimal comparison
    Z3_rcf_neq(ctx, inf_small, zero);  // Test infinitesimal comparison

    // Test string conversion (both compact and verbose)
    Z3_string str_one = Z3_rcf_num_to_string(ctx, one, true, false);
    assert(str_one != nullptr && strlen(str_one) > 0);

    Z3_string str_one_verbose = Z3_rcf_num_to_string(ctx, one, false, false);
    assert(str_one_verbose != nullptr && strlen(str_one_verbose) > 0);

    Z3_string str_pi = Z3_rcf_num_to_string(ctx, pi, true, false);
    assert(str_pi != nullptr && strlen(str_pi) > 0);

    Z3_string str_e = Z3_rcf_num_to_string(ctx, e, true, false);
    assert(str_e != nullptr && strlen(str_e) > 0);

    // Test HTML string conversion
    Z3_string str_pi_html = Z3_rcf_num_to_string(ctx, pi, true, true);
    assert(str_pi_html != nullptr && strlen(str_pi_html) > 0);

    // Test decimal conversion with different precisions
    Z3_string dec_half = Z3_rcf_num_to_decimal_string(ctx, half, 5);
    assert(dec_half != nullptr && strlen(dec_half) > 0);

    Z3_string dec_quarter = Z3_rcf_num_to_decimal_string(ctx, quarter, 10);
    assert(dec_quarter != nullptr && strlen(dec_quarter) > 0);

    Z3_string dec_pi = Z3_rcf_num_to_decimal_string(ctx, pi, 15);
    assert(dec_pi != nullptr && strlen(dec_pi) > 0);

    // Test numerator/denominator extraction
    Z3_rcf_num num, den;
    Z3_rcf_get_numerator_denominator(ctx, half, &num, &den);
    assert(num != nullptr && den != nullptr);

    Z3_rcf_num num2, den2;
    Z3_rcf_get_numerator_denominator(ctx, three_halves, &num2, &den2);
    assert(num2 != nullptr && den2 != nullptr);

    // Test polynomial root finding
    // Create polynomial x - 1 (has root 1)
    Z3_rcf_num linear_coeffs[2];
    linear_coeffs[0] = Z3_rcf_mk_small_int(ctx, -1); // constant term -1
    linear_coeffs[1] = Z3_rcf_mk_small_int(ctx, 1);  // x term 1

    Z3_rcf_num linear_roots[1];
    unsigned num_linear_roots = Z3_rcf_mk_roots(ctx, 2, linear_coeffs, linear_roots);
    assert(num_linear_roots == 1); // Should find exactly 1 root

    // Verify the root is correct (should be 1)
    assert(Z3_rcf_eq(ctx, linear_roots[0], one));

    // Test quadratic polynomial x^2 - 4 (has roots ±2)
    Z3_rcf_num quad_coeffs[3];
    quad_coeffs[0] = Z3_rcf_mk_small_int(ctx, -4); // constant term -4
    quad_coeffs[1] = Z3_rcf_mk_small_int(ctx, 0);  // x term 0
    quad_coeffs[2] = Z3_rcf_mk_small_int(ctx, 1);  // x^2 term 1

    Z3_rcf_num quad_roots[2];
    unsigned num_quad_roots = Z3_rcf_mk_roots(ctx, 3, quad_coeffs, quad_roots);
    assert(num_quad_roots == 2); // Should find exactly 2 roots

    // Clean up coefficient arrays
    Z3_rcf_del(ctx, linear_coeffs[0]);
    Z3_rcf_del(ctx, linear_coeffs[1]);
    Z3_rcf_del(ctx, quad_coeffs[0]);
    Z3_rcf_del(ctx, quad_coeffs[1]);
    Z3_rcf_del(ctx, quad_coeffs[2]);

    // Clean up root arrays
    for (unsigned i = 0; i < num_linear_roots; i++) {
        Z3_rcf_del(ctx, linear_roots[i]);
    }
    for (unsigned i = 0; i < num_quad_roots; i++) {
        Z3_rcf_del(ctx, quad_roots[i]);
    }

    // Clean up all RCF numbers
    Z3_rcf_del(ctx, zero);
    Z3_rcf_del(ctx, one);
    Z3_rcf_del(ctx, two);
    Z3_rcf_del(ctx, neg_one);
    Z3_rcf_del(ctx, half);
    Z3_rcf_del(ctx, quarter);
    Z3_rcf_del(ctx, three_halves);
    Z3_rcf_del(ctx, pi);
    Z3_rcf_del(ctx, e);
    Z3_rcf_del(ctx, inf_small);
    Z3_rcf_del(ctx, sum);
    Z3_rcf_del(ctx, diff);
    Z3_rcf_del(ctx, prod);
    Z3_rcf_del(ctx, quot);
    Z3_rcf_del(ctx, neg);
    Z3_rcf_del(ctx, inv);
    Z3_rcf_del(ctx, pow2);
    Z3_rcf_del(ctx, pow3);
    Z3_rcf_del(ctx, num);
    Z3_rcf_del(ctx, den);
    Z3_rcf_del(ctx, num2);
    Z3_rcf_del(ctx, den2);

    Z3_del_context(ctx);

    std::cout << "RCF API tests passed!\n";
}