
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

// Checks that the IEEE 754-2019 recommended transcendental operations
// (Section 9.2) simplify correctly for the special values that every
// conforming implementation must agree on (there is no mandated
// correctly-rounded result for these operations in general, so we don't
// test regular finite arguments).
static void test_transcendental_rewriter_specials() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* spec =
        "(declare-const one (_ FloatingPoint 11 53))\n"
        "(assert (= one ((_ to_fp 11 53) RNE 1.0)))\n"
        "(assert (not (fp.eq (fp.exp RNE (_ +zero 11 53)) one)))\n"
        "(check-sat-using (then simplify smt))\n";
    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << "exp(+0)=1: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec2 =
        "(assert (not (fp.isNaN (fp.sin RNE (_ NaN 8 24)))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec2);
    if (response.find("unsat") == std::string::npos)
        std::cout << "sin(NaN)=NaN: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec3 =
        "(assert (not (fp.isNaN (fp.sin RNE (_ +oo 8 24)))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec3);
    if (response.find("unsat") == std::string::npos)
        std::cout << "sin(+oo)=NaN: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec4 =
        "(assert (not (= (fp.cos RNE (_ +zero 8 24)) ((_ to_fp 8 24) RNE 1.0))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec4);
    if (response.find("unsat") == std::string::npos)
        std::cout << "cos(+0)=1: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec5 =
        "(assert (not (= (fp.log RNE ((_ to_fp 8 24) RNE 1.0)) (_ +zero 8 24))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec5);
    if (response.find("unsat") == std::string::npos)
        std::cout << "log(1)=+0: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec6 =
        "(declare-const x6 (_ FloatingPoint 8 24))\n"
        "(assert (not (= (fp.pow RNE x6 (_ +zero 8 24)) ((_ to_fp 8 24) RNE 1.0))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec6);
    if (response.find("unsat") == std::string::npos)
        std::cout << "pow(x,+0)=1: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec7 =
        "(declare-const x7 (_ FloatingPoint 8 24))\n"
        "(assert (not (= (fp.pow RNE x7 ((_ to_fp 8 24) RNE 1.0)) x7)))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec7);
    if (response.find("unsat") == std::string::npos)
        std::cout << "pow(x,1)=x: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec8 =
        "(declare-const x8 (_ FloatingPoint 8 24))\n"
        "(assert (not (= (fp.hypot RNE x8 (_ +zero 8 24)) (fp.abs x8))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec8);
    if (response.find("unsat") == std::string::npos)
        std::cout << "hypot(x,+0)=|x|: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    char const* spec9 =
        "(declare-const y (_ FloatingPoint 8 24))\n"
        "(assert (not (fp.isNaN (fp.atan2 RNE (_ NaN 8 24) y))))\n"
        "(check-sat-using (then simplify smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec9);
    if (response.find("unsat") == std::string::npos)
        std::cout << "atan2(NaN,y)=NaN: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

// Checks that the new transcendental operations translate into
// well-sorted bit-vector formulas (fpa2bv) and that repeated applications
// of the same operator to (semantically) equal arguments are recognized
// as equal, as required for any deterministic function -- interpreted
// or, as here, translated into a fresh uninterpreted bit-vector function.
static void test_transcendental_fpa2bv() {
    // Congruence: equal arguments must give equal results. This is
    // checked through the SMT kernel's native FPA theory (theory_fpa),
    // which shares the same fpa2bv_converter::mk_uf translation used by
    // the fpa2bv *tactic*. (The standalone fpa2bv/bit-blast tactic chain
    // has a pre-existing, unrelated limitation with RoundingMode-sorted
    // UF arguments that also affects ordinary user-declared functions,
    // so congruence is checked via plain (check-sat) here instead.)
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    char const* spec =
        "(declare-const x (_ FloatingPoint 8 24))\n"
        "(declare-const y (_ FloatingPoint 8 24))\n"
        "(assert (= x y))\n"
        "(assert (not (= (fp.sin RNE x) (fp.sin RNE y))))\n"
        "(check-sat)\n";
    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << "fp.sin congruence: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);
    Z3_del_context(ctx);

    cfg = Z3_mk_config();
    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    char const* spec2 =
        "(declare-const x (_ FloatingPoint 8 24))\n"
        "(declare-const y (_ FloatingPoint 8 24))\n"
        "(assert (= x y))\n"
        "(assert (not (= (fp.pow RNE x x) (fp.pow RNE y y))))\n"
        "(check-sat)\n";
    response = Z3_eval_smtlib2_string(ctx, spec2);
    if (response.find("unsat") == std::string::npos)
        std::cout << "fp.pow congruence: " << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);
    Z3_del_context(ctx);

    // fp.exp is satisfiable both ways when unconstrained by special
    // values: it is translated as an uninterpreted function, so nothing
    // prevents the solver from picking a NaN result for a generic input.
    cfg = Z3_mk_config();
    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    char const* spec3 =
        "(declare-const x (_ FloatingPoint 8 24))\n"
        "(assert (not (fp.isNaN x)))\n"
        "(assert (fp.isNaN (fp.exp RNE x)))\n"
        "(check-sat)\n";
    response = Z3_eval_smtlib2_string(ctx, spec3);
    if (response.find("unsat") != std::string::npos || response.find("sat") == std::string::npos)
        std::cout << "fp.exp uninterpreted (expect sat): " << response << "\n";
    ENSURE(response.find("unsat") == std::string::npos && response.find("sat") != std::string::npos);
    Z3_del_context(ctx);

    // Sanity check that the standalone fpa2bv tactic (used e.g. for
    // preprocessing before bit-blasting) produces a well-sorted formula
    // for the new operators and that the resulting problem is solvable.
    cfg = Z3_mk_config();
    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    char const* spec4 =
        "(declare-const x (_ FloatingPoint 8 24))\n"
        "(assert (fp.gt (fp.sin RNE x) (_ +zero 8 24)))\n"
        "(check-sat-using (then fpa2bv simplify bit-blast smt))\n";
    response = Z3_eval_smtlib2_string(ctx, spec4);
    if (response.find("sat") == std::string::npos)
        std::cout << "fp.sin fpa2bv well-sortedness: " << response << "\n";
    ENSURE(response.find("sat") != std::string::npos);


    Z3_del_context(ctx);
}

void tst_fpa() {
    test_rem_subnormal_divisor();
    test_is_inf_large_significand();
    test_significand_out_of_range();
    test_transcendental_rewriter_specials();
    test_transcendental_fpa2bv();
}
