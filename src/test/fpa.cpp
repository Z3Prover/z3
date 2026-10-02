
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

static void test_to_fp_real_rounding_carry() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // to_fp from a symbolic Real must account for a rounding carry into
    // the next binade: any r in [2 - 2^-24, 2) rounds to 2.0 under RNE.
    // See https://github.com/Z3Prover/z3/issues/10931
    char const* sat_spec =
        "(set-logic ALL)\n"
        "(declare-fun r () Real)\n"
        "(declare-fun c () (_ FloatingPoint 8 24))\n"
        "(assert (< r 2.0))\n"
        "(assert (= c ((_ to_fp 8 24) roundNearestTiesToEven r)))\n"
        "(assert (= c (fp #b0 #x80 #b00000000000000000000000)))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, sat_spec);
    if (response.find("sat") == std::string::npos || response.find("unsat") != std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") == std::string::npos);
    ENSURE(response.find("sat") != std::string::npos);

    Z3_del_context(ctx);

    // r strictly below the largest float less than 2.0 cannot round up to
    // 2.0, so this must remain unsat.
    cfg = Z3_mk_config();
    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* unsat_spec =
        "(set-logic ALL)\n"
        "(declare-fun r () Real)\n"
        "(declare-fun c () (_ FloatingPoint 8 24))\n"
        "(assert (< r (/ 33554430.0 16777216.0)))\n"
        "(assert (= c ((_ to_fp 8 24) roundNearestTiesToEven r)))\n"
        "(assert (= c (fp #b0 #x80 #b00000000000000000000000)))\n"
        "(check-sat)\n";

    response = Z3_eval_smtlib2_string(ctx, unsat_spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

void tst_fpa() {
    test_rem_subnormal_divisor();
    test_is_inf_large_significand();
    test_significand_out_of_range();
    test_to_fp_real_rounding_carry();
}

