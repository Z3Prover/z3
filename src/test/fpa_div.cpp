
/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    fpa_div.cpp

Abstract:

    Unit tests for floating-point division normalization (PR #10216).

    The fix corrects leading-zero counting in symbolic fp.div for formats
    where 2^ebits < sbits (e.g., FP(2,6), FP(2,5)).  In those formats the
    old code used an ebits-wide bitvector for the leading-zero count, which
    could wrap around and produce an incorrect result; the fix widens the
    bitvector to hold the actual maximum count.

    Regression for issue #10175.

--*/

#include "api/z3.h"
#include "util/debug.h"
#include <iostream>

static Z3_context mk_ctx() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    return ctx;
}

// Parse the assertions from an SMT-LIB2 string, add them to a fresh solver,
// and return the satisfiability result.
static Z3_lbool check_smt2(Z3_context ctx, const char * smt2) {
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_ast_vector av = Z3_parse_smtlib2_string(ctx, smt2, 0, nullptr, nullptr, 0, nullptr, nullptr);
    Z3_ast_vector_inc_ref(ctx, av);

    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, av); ++i)
        Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx, av, i));

    Z3_lbool result = Z3_solver_check(ctx, s);
    Z3_ast_vector_dec_ref(ctx, av);
    Z3_solver_dec_ref(ctx, s);
    return result;
}

// Issue #10175 exact reproducer.
// FP(2,6): ebits=2, sbits=6, so 2^ebits = 4 < 6 = sbits → wide-lz path.
//
// Mathematically: (-3.25) / 0.0625 = -52.
// In FP(2,6) the maximum finite magnitude is 3.9375, so -52 overflows.
// With RTZ (round toward zero) overflow maps to the most-negative-normal
// (-3.9375), NOT to -infinity.
// Therefore (fp.eq -inf (fp.div RTZ c b)) must be UNSAT.
static void test_fp26_div_not_infinity() {
    std::cout << "test_fp26_div_not_infinity\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun c () (_ FloatingPoint 2 6)"
        "   ((_ to_fp 2 6) RTZ (- 3.25)))\n"
        "(define-fun b () (_ FloatingPoint 2 6)"
        "   ((_ to_fp 2 6) RTZ 0.0625))\n"
        "(assert (fp.eq (_ -oo 2 6) (fp.div RTZ c b)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_FALSE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(2,6): RTZ overflow clips to the most-negative normal value, not -oo.
// (-3.25) / 0.0625 = -52 overflows; RTZ result = -(2 - 2^-5) * 2^1 = -3.9375.
static void test_fp26_div_rtz_clips_to_max_negative() {
    std::cout << "test_fp26_div_rtz_clips_to_max_negative\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun c () (_ FloatingPoint 2 6)"
        "   ((_ to_fp 2 6) RTZ (- 3.25)))\n"
        "(define-fun b () (_ FloatingPoint 2 6)"
        "   ((_ to_fp 2 6) RTZ 0.0625))\n"
        "(define-fun expected () (_ FloatingPoint 2 6)"
        "   ((_ to_fp 2 6) RTZ (- 3.9375)))\n"
        "(assert (fp.eq expected (fp.div RTZ c b)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(2,6): Exact division in the representable range (no rounding needed).
// 2.0 / 1.0 = 2.0 in any format.
static void test_fp26_div_exact() {
    std::cout << "test_fp26_div_exact\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun two () (_ FloatingPoint 2 6) ((_ to_fp 2 6) RNE 2.0))\n"
        "(define-fun one () (_ FloatingPoint 2 6) ((_ to_fp 2 6) RNE 1.0))\n"
        "(assert (fp.eq two (fp.div RNE two one)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(2,6): Division whose dividend is a denormal value.
// 0.0625 is denormal in FP(2,6) (below the minimum normal 1.0).
// 0.0625 / 0.0625 = 1.0 exactly.
static void test_fp26_div_denormal_by_self() {
    std::cout << "test_fp26_div_denormal_by_self\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun d () (_ FloatingPoint 2 6) ((_ to_fp 2 6) RTZ 0.0625))\n"
        "(define-fun one () (_ FloatingPoint 2 6) ((_ to_fp 2 6) RNE 1.0))\n"
        "(assert (fp.eq one (fp.div RNE d d)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(2,6): Dividing the most-negative-normal by itself gives -1.0.
// -3.9375 / -3.9375 = 1.0 (positive, same as any x/x with x != 0).
// Wait: (-3.9375) / (-3.9375) = 1.0.
static void test_fp26_div_max_neg_by_self() {
    std::cout << "test_fp26_div_max_neg_by_self\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun m () (_ FloatingPoint 2 6) ((_ to_fp 2 6) RTZ (- 3.9375)))\n"
        "(define-fun one () (_ FloatingPoint 2 6) ((_ to_fp 2 6) RNE 1.0))\n"
        "(assert (fp.eq one (fp.div RNE m m)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(2,5): Another format with 2^ebits < sbits (2^2 = 4 < 5).
// 1.0 / 1.0 = 1.0.
static void test_fp25_div_basic() {
    std::cout << "test_fp25_div_basic\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun one () (_ FloatingPoint 2 5) ((_ to_fp 2 5) RNE 1.0))\n"
        "(assert (fp.eq one (fp.div RNE one one)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(2,5): Overflow with RNE rounds to +oo.
// Max normal in FP(2,5): (2 - 2^-4) * 2^1 = 3.875
// 3.875 / 0.125 = 31.0 overflows; RNE → +oo.
static void test_fp25_div_overflow_rne() {
    std::cout << "test_fp25_div_overflow_rne\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun n () (_ FloatingPoint 2 5) ((_ to_fp 2 5) RNE 3.875))\n"
        "(define-fun d () (_ FloatingPoint 2 5) ((_ to_fp 2 5) RNE 0.125))\n"
        "(assert (fp.eq (_ +oo 2 5) (fp.div RNE n d)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// Float32 backward-compatibility: 2^8 = 256 > 24 = sbits, old code path.
// 6.0 / 2.0 = 3.0 exactly.
static void test_fp32_div_basic() {
    std::cout << "test_fp32_div_basic\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(assert (fp.eq ((_ to_fp 8 24) RNE 3.0)\n"
        "               (fp.div RNE ((_ to_fp 8 24) RNE 6.0)\n"
        "                           ((_ to_fp 8 24) RNE 2.0))))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// Float16 backward-compatibility: 2^5 = 32 > 11 = sbits, old code path.
// 1.0 / 2.0 = 0.5 exactly.
static void test_fp16_div_basic() {
    std::cout << "test_fp16_div_basic\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(assert (fp.eq ((_ to_fp 5 11) RNE 0.5)\n"
        "               (fp.div RNE ((_ to_fp 5 11) RNE 1.0)\n"
        "                           ((_ to_fp 5 11) RNE 2.0))))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

// FP(3,8): boundary case where 2^ebits = sbits (2^3 = 8), old code path.
// 1.0 / 1.0 = 1.0.
static void test_fp38_div_basic() {
    std::cout << "test_fp38_div_basic\n";
    Z3_context ctx = mk_ctx();

    const char * smt2 =
        "(define-fun one () (_ FloatingPoint 3 8) ((_ to_fp 3 8) RNE 1.0))\n"
        "(assert (fp.eq one (fp.div RNE one one)))\n";

    ENSURE(check_smt2(ctx, smt2) == Z3_L_TRUE);
    std::cout << "  PASSED\n";
    Z3_del_context(ctx);
}

void tst_fpa_div() {
    test_fp26_div_not_infinity();
    test_fp26_div_rtz_clips_to_max_negative();
    test_fp26_div_exact();
    test_fp26_div_denormal_by_self();
    test_fp26_div_max_neg_by_self();
    test_fp25_div_basic();
    test_fp25_div_overflow_rne();
    test_fp32_div_basic();
    test_fp16_div_basic();
    test_fp38_div_basic();
}
