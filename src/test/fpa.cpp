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

void tst_fpa() {
    test_fp_to_real_denormal();
}
