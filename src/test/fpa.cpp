/*++
Copyright (c) 2025 Microsoft Corporation

--*/

// Regression tests for floating-point arithmetic encoding and model generation.

#include "api/z3.h"
#include "util/debug.h"
#include <string.h>

static void run_fp_test(const char * assertion, bool expect_sat) {
    Z3_context ctx = Z3_mk_context(nullptr);
    const char * result = Z3_eval_smtlib2_string(ctx, assertion);
    if (expect_sat) {
        ENSURE(strstr(result, "sat") != nullptr);
        ENSURE(strstr(result, "unsat") == nullptr);
    } else {
        ENSURE(strstr(result, "unsat") != nullptr);
    }
    ENSURE(strstr(result, "invalid") == nullptr);
    Z3_del_context(ctx);
}

// Test that fp.to_real produces correct values for denormal floating-point numbers.
// Regression test for: incorrect model with (_ FloatingPoint 2 24) and fp.to_real.
// Denormal numbers require subtracting the normalization shift (lz) from the exponent;
// without this fix, denormals in fp.to_real were ~2^lz times too large.
static void test_fp_to_real_denormal() {
    // Test 1: the specific denormal from the bug report (fp #b0 #b00 #b00111011011111001011101)
    // has fp.to_real ~= 0.232, which must NOT be > 1.0
    run_fp_test(
        "(set-option :model_validate true)\n"
        "(assert (> (fp.to_real (fp #b0 #b00 #b00111011011111001011101)) 1.0))\n"
        "(check-sat)\n",
        false);

    // Test 2: denormal with leading significand bit = 1, fp.to_real should be 0.5
    // (fp #b0 #b00 #b10000000000000000000000) in (_ FloatingPoint 2 24)
    run_fp_test(
        "(set-option :model_validate true)\n"
        "(assert (= (fp.to_real (fp #b0 #b00 #b10000000000000000000000)) (/ 1.0 2.0)))\n"
        "(check-sat)\n",
        true);

    // Test 3: denormal with significand bit pattern giving fp.to_real = 0.125
    // (fp #b0 #b00 #b00100000000000000000000) in (_ FloatingPoint 2 24)
    run_fp_test(
        "(set-option :model_validate true)\n"
        "(assert (= (fp.to_real (fp #b0 #b00 #b00100000000000000000000)) (/ 1.0 8.0)))\n"
        "(check-sat)\n",
        true);

    // Test 4: a normal value (fp #b0 #b01 #b11111111111111111111111) must be > 1.0
    // This is the maximum finite normal number in (_ FloatingPoint 2 24)
    run_fp_test(
        "(set-option :model_validate true)\n"
        "(assert (> (fp.to_real (fp #b0 #b01 #b11111111111111111111111)) 1.0))\n"
        "(check-sat)\n",
        true);
}

// Regression test for soundness bug in to_fp (from real) with symbolic real interval.
// When the rounding mode is RTZ and the real variable is constrained to an interval
// that includes the exact rational value of a float, Z3 should return SAT.
// This was broken because mk_to_real computed 2^(1/|exp|) instead of 1/(2^|exp|)
// for floats with negative exponents, causing a conflict in the NRA solver.
static void test_to_fp_from_real_interval() {
    // The interval (-4127125/16777216, -16508499/67108864] contains -16508499/67108864
    // which is the exact rational value of fp #b1 #b01111100 #b11110111110011001010011.
    // to_fp(RTZ, r) for r in this closed interval must equal that float.
    run_fp_test(
        "(set-logic QF_FPLRA)\n"
        "(declare-const x Float32)\n"
        "(assert (= x (fp #b1 #b01111100 #b11110111110011001010011)))\n"
        "(declare-const r Real)\n"
        "(assert (and (> r (- (/ 4127125.0 16777216.0))) (<= r (- (/ 16508499.0 67108864.0)))))\n"
        "(declare-const w Float32)\n"
        "(assert (= w ((_ to_fp 8 24) RTZ r)))\n"
        "(assert (= x w))\n"
        "(check-sat)\n",
        true);
}

// Preserve the signed value of the internal exponent when converting a symbolic
// unsigned bit-vector. In-range values must not take the overflow path.
static void test_to_fp_unsigned_exponent_width_boundary() {
    run_fp_test(
        "(set-logic QF_BVFP)\n"
        "(set-option :model_validate true)\n"
        "(declare-const high (_ BitVec 13))\n"
        "(assert (or (= high #b1111111111110) (= high #b1111111111111)))\n"
        "(assert (= ((_ to_fp_unsigned 2 11) RTN high) (fp #b0 #b10 #b1111111111)))\n"
        "(assert (= ((_ to_fp_unsigned 2 11) RTZ high) (fp #b0 #b10 #b1111111111)))\n"
        "(assert (= ((_ to_fp_unsigned 2 11) RTP high) (_ +oo 2 11)))\n"
        "(assert (= ((_ to_fp_unsigned 2 11) RNE high) (_ +oo 2 11)))\n"
        "(assert (= ((_ to_fp_unsigned 2 11) RNA high) (_ +oo 2 11)))\n"
        "(declare-const small (_ BitVec 13))\n"
        "(assert (or (= small #b0000000000001) (= small #b0000000000010)))\n"
        "(assert (= ((_ to_fp_unsigned 2 11) RTN small)\n"
        "           (ite (= small #b0000000000001)\n"
        "                (fp #b0 #b01 #b0000000000)\n"
        "                (fp #b0 #b10 #b0000000000))))\n"
        "(check-sat)\n",
        true);
}

static void test_to_fp_unsigned_common_widths() {
    run_fp_test(
        "(set-logic QF_BVFP)\n"
        "(set-option :model_validate true)\n"
        "(declare-const high (_ BitVec 32))\n"
        "(assert (or (= high #xfffffffe) (= high #xffffffff)))\n"
        "(assert (= ((_ to_fp_unsigned 8 24) RTN high)\n"
        "           (fp #b0 #b10011110 #b11111111111111111111111)))\n"
        "(assert (= ((_ to_fp_unsigned 8 24) RTZ high)\n"
        "           (fp #b0 #b10011110 #b11111111111111111111111)))\n"
        "(assert (= ((_ to_fp_unsigned 8 24) RTP high)\n"
        "           (fp #b0 #b10011111 #b00000000000000000000000)))\n"
        "(assert (= ((_ to_fp_unsigned 8 24) RNE high)\n"
        "           (fp #b0 #b10011111 #b00000000000000000000000)))\n"
        "(assert (= ((_ to_fp_unsigned 8 24) RNA high)\n"
        "           (fp #b0 #b10011111 #b00000000000000000000000)))\n"
        "(check-sat)\n",
        true);
}

static void test_recfun_defined_function_soundness() {
    run_fp_test(
        "(set-option :model_validate true)\n"
        "(declare-fun fixedAdd () Int)\n"
        "(declare-fun variableAdd () Int)\n"
        "(define-fun-rec $$add$$ ((a Int) (b Int)) Int\n"
        "  (ite (= 0 b) 2 (- a (+ 0 (- fixedAdd b)))))\n"
        "(assert (= fixedAdd (* 9 fixedAdd)))\n"
        "(assert (= 1 ($$add$$ 1 3)))\n"
        "(check-sat)\n",
        false);
}

void tst_fpa() {
    test_fp_to_real_denormal();
    test_to_fp_from_real_interval();
    test_to_fp_unsigned_exponent_width_boundary();
    test_to_fp_unsigned_common_widths();
    test_recfun_defined_function_soundness();
}
