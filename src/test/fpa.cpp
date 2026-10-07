
/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "api/z3.h"
#include "util/debug.h"
#include <iostream>
#include <string>

static void test_rem_subnormal_divisor() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* spec =
        "(declare-const x (_ FloatingPoint 5 11))\n"
        "(declare-const y (_ FloatingPoint 5 11))\n"
        "(assert (= x ((_ to_fp 5 11) #b1110100000101010)))\n"
        "(assert (= y ((_ to_fp 5 11) #b1000000000010101)))\n"
        "(assert (not (= ((_ fp.to_ieee_bv 16) (fp.rem x y)) #x000a)))\n"
        "(check-sat-using (then fpa2bv simplify bit-blast smt))\n";

    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

static void test_is_inf_large_significand() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* constant_spec =
        "(set-logic ALL)\n"
        "(assert (not (fp.isInfinite ((_ to_fp 2 65535) RNE (to_real 4)))))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, constant_spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* symbolic_spec =
        "(declare-const x Int)\n"
        "(assert (= x 4))\n"
        "(assert (not (fp.isInfinite ((_ to_fp 2 65535) RNE (to_real x)))))\n"
        "(check-sat)\n";

    response = Z3_eval_smtlib2_string(ctx, symbolic_spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

static void ignore_error(Z3_context, Z3_error_code) {}

static void test_significand_out_of_range() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(ctx, ignore_error);

    // mpf cannot represent formats with more than MPF_MAX_SBITS significand
    // bits; such formats have to be rejected instead of silently truncated.
    char const* spec =
        "(declare-const x (_ FloatingPoint 2 65536))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    ENSURE(response.find("maximum number of significand bits") != std::string::npos);

    Z3_del_context(ctx);
}

static void test_inexact_symbolic_to_fp_real() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
      // Converting a symbolic real to a float is inexact in general; requiring an
    // exact round-trip used to produce a spurious unsat.
    char const* inexact_spec =
        "(set-logic ALL)\n"
        "(declare-const x Real)\n"
        "(declare-const rounded (_ FloatingPoint 5 11))\n"
        "(assert (not (fp.isNaN rounded)))\n"
        "(assert (not (fp.isInfinite rounded)))\n"
        "(assert (fp.eq rounded ((_ to_fp 5 11) RNE x)))\n"
        "(assert (distinct (fp.to_real rounded) x))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, inexact_spec);
    if (response.find("sat") == std::string::npos || response.find("unsat") != std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") == std::string::npos);
    ENSURE(response.find("sat") != std::string::npos);

    // The rounding of a symbolic real still has to agree with the rounding of the
    // corresponding numeral, for every rounding mode.
    char const* rounding_spec =
        "(reset)\n"
        "(declare-const y Real)\n"
        "(assert (= y (/ 23.0 128.0)))\n"
        "(assert (or (not (= ((_ to_fp 3 4) RNE y) ((_ to_fp 3 4) RNE (/ 23.0 128.0))))\n"
        "            (not (= ((_ to_fp 3 4) RNA y) ((_ to_fp 3 4) RNA (/ 23.0 128.0))))\n"
        "            (not (= ((_ to_fp 3 4) RTP y) ((_ to_fp 3 4) RTP (/ 23.0 128.0))))\n"
        "            (not (= ((_ to_fp 3 4) RTN y) ((_ to_fp 3 4) RTN (/ 23.0 128.0))))\n"
        "            (not (= ((_ to_fp 3 4) RTZ y) ((_ to_fp 3 4) RTZ (/ 23.0 128.0))))))\n"
        "(check-sat)\n";

    response = Z3_eval_smtlib2_string(ctx, rounding_spec);

      if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);
    Z3_del_context(ctx);
}

static void test_to_fp_real_zero_sign() {

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);


    // Converting the mathematical real 0 must always yield +0, never -0,
    // regardless of rounding mode: a real number carries no sign bit for
    // the rounding mode to act on. This used to produce an invalid model
    // (issue #7431) because the old encoding allowed either +0 or -0 when
    // the input was exactly 0.
    char const* zero_spec =
        "(set-logic ALL)\n"
        "(declare-const v Real)\n"
        "(assert (= v 0.0))\n"
        "(assert (= ((_ to_fp 2 6) RTZ v) (fp (_ bv1 1) (_ bv0 2) (_ bv0 5))))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, zero_spec);

    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

      // The original #7431 reproducer uses a *symbolic* free real `v`; whether
    // that query is `sat` in general additionally depends on the (separate,
    // still-open) symbolic-rounding completeness bug tracked by issues
    // #10881/#10931. This test only re-checks the invalid-model regression
    // above. As a sanity check that negative-zero results are still
    // reachable at all post-fix, a concrete small negative numeral (which
    // goes through the unrelated, already-correct numeral-rounding code
    // path) must still round to -0 under RTZ.
    char const* numeral_spec =
        "(reset)\n"
        "(set-logic ALL)\n"
        "(assert (= ((_ to_fp 2 6) RTZ (- 0.0001)) (fp (_ bv1 1) (_ bv0 2) (_ bv0 5))))\n"
        "(check-sat)\n";

    response = Z3_eval_smtlib2_string(ctx, numeral_spec);
    if (response.find("unsat") != std::string::npos || response.find("sat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") == std::string::npos);
    ENSURE(response.find("sat") != std::string::npos);

    // Rounding toward zero saturates at the largest finite value.
    char const* overflow_spec =
        "(reset)\n"
        "(declare-const z Real)\n"
        "(assert (= z 1000.0))\n"
        "(assert (not (= ((_ to_fp 3 4) RTZ z) ((_ to_fp 3 4) RTZ 15.0))))\n"
        "(check-sat)\n";

    response = Z3_eval_smtlib2_string(ctx, overflow_spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);


    Z3_del_context(ctx);
}

void tst_fpa() {
    test_rem_subnormal_divisor();
    test_is_inf_large_significand();
    test_significand_out_of_range();
    test_to_fp_real_zero_sign();
    test_inexact_symbolic_to_fp_real();
}
