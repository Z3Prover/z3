/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    proof_replay.cpp

Abstract:

    Regression tests for replaying sat.smt clause proof logs through the
    built-in checkers: numerals as the SMT-LIB printer emits them, and the
    n-ary arithmetic shapes the arithmetic checker linearizes.

--*/
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/extra_cmds/proof_cmds.h"
#include "parsers/smt2/smt2parser.h"
#include "sat/smt/arith_theory_checker.h"
#include <iostream>
#include <sstream>

// Replay a clause proof log and return what the checker printed.
static std::string replay(char const* log) {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context ctx(false, &m);
    install_proof_cmds(ctx);
    std::istringstream is(log);
    std::ostringstream captured;
    std::streambuf* saved = std::cout.rdbuf(captured.rdbuf());
    bool ok = parse_smt2_commands(ctx, is);
    std::cout.rdbuf(saved);
    VERIFY(ok);
    return captured.str();
}

static void check_verified_natively(std::string const& out, char const* hint) {
    std::cout << out;
    ENSURE(out.find("(verified-smt") == std::string::npos);
    ENSURE(out.find("did not verify") == std::string::npos);
    ENSURE(out.find("is not rup") == std::string::npos);
    ENSURE(out.find(std::string("+") + hint) != std::string::npos);
}

// The log z3 writes under sat.smt=true for
//   (declare-const x Real) (declare-const y Real)
//   (assert (>= (- x y) (/ 1.0 3.0))) (assert (<= (- x y) (/ 1.0 4.0)))
// The Real constants come back from the printer as divisions.
static char const* farkas_real_log =
    "(declare-fun k!1 () Real)\n"
    "(define-const $24 Bool (>= k!1 (/ 1.0 3.0)))\n"
    "(assume $24)\n"
    "(define-const $27 Bool (<= k!1 (/ 1.0 4.0)))\n"
    "(assume $27)\n"
    "(declare-fun farkas (Int Bool Int Bool) Proof)\n"
    "(define-const $31 Proof (farkas 1 $27 1 $24))\n"
    "(infer $31)\n"
    "(declare-fun rup () Proof)\n"
    "(infer rup)\n";

// Negative integers are printed as (- n).
static char const* farkas_int_log =
    "(declare-fun k!1 () Int)\n"
    "(define-const $1 Bool (>= k!1 (- 2)))\n"
    "(assume $1)\n"
    "(define-const $2 Bool (<= k!1 (- 3)))\n"
    "(assume $2)\n"
    "(declare-fun farkas (Int Bool Int Bool) Proof)\n"
    "(define-const $3 Proof (farkas 1 $2 1 $1))\n"
    "(infer $3)\n"
    "(declare-fun rup () Proof)\n"
    "(infer rup)\n";

static char const* farkas_to_int_log =
    "(declare-fun x () Int)\n"
    "(define-const $1 Bool (>= x (to_int (/ (- 7.0) 3.0))))\n"
    "(assume $1)\n"
    "(define-const $2 Bool (<= x (- 4)))\n"
    "(assume $2)\n"
    "(declare-fun farkas (Int Bool Int Bool) Proof)\n"
    "(define-const $3 Proof (farkas 1 $2 1 $1))\n"
    "(infer $3)\n"
    "(declare-fun rup () Proof)\n"
    "(infer rup)\n";

// The same problem logged with smt.solve_eqs, smt.propagate_values, and
// smt.elim_unconstrained off. The literals contain (* (- 1.0) y), so folding
// produces terms that exist nowhere else in the log; the RUP checker must keep
// them alive, or their ids are reused and the units are reported as not RUP.
static char const* farkas_nopp_log =
    "(declare-fun y () Real)\n"
    "(declare-fun x () Real)\n"
    "(define-const $16 Real (* (- 1.0) y))\n"
    "(define-const $17 Real (+ x $16))\n"
    "(define-const $21 Bool (>= $17 (/ 1.0 3.0)))\n"
    "(assume $21)\n"
    "(define-const $19 Bool (<= $17 (/ 1.0 4.0)))\n"
    "(assume $19)\n"
    "(declare-fun farkas (Int Bool Int Bool) Proof)\n"
    "(define-const $25 Proof (farkas 1 $19 1 $21))\n"
    "(infer $25)\n"
    "(declare-fun rup () Proof)\n"
    "(infer rup)\n";

static void tst_replay_folds_printed_numerals() {
    check_verified_natively(replay(farkas_real_log), "farkas 1");
    check_verified_natively(replay(farkas_int_log), "farkas 1");
    check_verified_natively(replay(farkas_to_int_log), "farkas 1");
    check_verified_natively(replay(farkas_nopp_log), "farkas 1");
}

// Parse the assertions of text, unsimplified, in order.
static expr_ref_vector parse_lits(ast_manager& m, char const* text) {
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::istringstream is(text);
    VERIFY(parse_smt2_commands(ctx, is));
    expr_ref_vector lits(m);
    for (expr* e : ctx.assertions())
        lits.push_back(e);
    return lits;
}

static app_ref mk_farkas(ast_manager& m, expr_ref_vector const& coeffs, expr_ref_vector const& lits) {
    ENSURE(coeffs.size() == lits.size());
    expr_ref_vector args(m);
    for (unsigned i = 0; i < lits.size(); ++i) {
        args.push_back(coeffs.get(i));
        args.push_back(lits.get(i));
    }
    return app_ref(m.mk_app(symbol("farkas"), args.size(), args.data(), m.mk_proof_sort()), m);
}

static expr_ref_vector ints(ast_manager& m, std::initializer_list<int> ns) {
    arith_util a(m);
    expr_ref_vector r(m);
    for (int n : ns)
        r.push_back(a.mk_int(n));
    return r;
}

// (* 2 3 x) is 6x: numeral factors of an n-ary product fold into the coefficient.
static void tst_checker_nary_mul() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector lits = parse_lits(m,
        "(declare-const x Real)"
        "(assert (>= (* 2.0 3.0 x) 1.0))(assert (<= x 0.0))");
    ENSURE(lits.size() == 2);
    ENSURE(to_app(to_app(lits.get(0))->get_arg(0))->get_num_args() == 3);
    arith::theory_checker checker(m);
    ENSURE(checker.check(mk_farkas(m, ints(m, {1, 6}), lits)));
    // x * y is nonlinear; the product stays one opaque term and the hint is not proven.
    lits = parse_lits(m,
        "(declare-const x Real)(declare-const y Real)"
        "(assert (>= (* 2.0 x y) 1.0))(assert (<= x 0.0))");
    ENSURE(!checker.check(mk_farkas(m, ints(m, {1, 2}), lits)));
}

// Printed numerals in literals and in hint coefficients are accepted without a replay fold.
static void tst_checker_printed_numerals() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref_vector lits = parse_lits(m,
        "(declare-const x Real)"
        "(assert (>= x (/ 1.0 3.0)))(assert (<= x (- (/ 1.0 4.0))))");
    ENSURE(a.is_div(to_app(lits.get(0))->get_arg(1)));
    expr_ref_vector coeffs(m);
    coeffs.push_back(a.mk_uminus(a.mk_int(1)));
    coeffs.push_back(a.mk_uminus(a.mk_int(1)));
    arith::theory_checker checker(m);
    ENSURE(checker.check(mk_farkas(m, coeffs, lits)));
}

static void tst_is_extended_numeral() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    rational n;
    expr_ref t(m);
    t = a.mk_real(7);
    ENSURE(a.is_extended_numeral(t, n) && n == 7);
    {
        expr_ref lhs(a.mk_uminus(a.mk_real(1)), m);
        expr_ref lhs1(a.mk_real(2), m);
        expr_ref rhs(a.mk_uminus(a.mk_real(4)), m);
        expr_ref rhs1(a.mk_div(lhs1, rhs), m);
        t = a.mk_div(lhs, rhs1);
    }
    ENSURE(a.is_extended_numeral(t, n) && n == 2);
    t = a.mk_to_real(a.mk_uminus(a.mk_int(3)));
    ENSURE(a.is_extended_numeral(t, n) && n == -3);
    {
        expr_ref lhs(a.mk_real(-7), m);
        expr_ref rhs(a.mk_real(3), m);
        t = a.mk_to_int(a.mk_div(lhs, rhs));
    }
    ENSURE(a.is_extended_numeral(t, n) && n == -3);
    {
        expr_ref lhs(a.mk_real(7), m);
        expr_ref rhs(a.mk_real(3), m);
        t = a.mk_to_real(a.mk_to_int(a.mk_div(lhs, rhs)));
    }
    ENSURE(a.is_extended_numeral(t, n) && n == 2);
    {
        expr_ref lhs(a.mk_real(1), m);
        expr_ref rhs(a.mk_real(0), m);
        t = a.mk_div(lhs, rhs);
    }
    ENSURE(!a.is_extended_numeral(t, n));
    {
        expr_ref lhs(a.mk_real(1), m);
        expr_ref rhs(a.mk_uminus(a.mk_real(0)), m);
        t = a.mk_div(lhs, rhs);
    }
    ENSURE(!a.is_extended_numeral(t, n));
    {
        expr_ref lhs(a.mk_real(1), m);
        expr_ref lhs1(a.mk_real(1), m);
        expr_ref rhs(a.mk_real(0), m);
        expr_ref rhs1(a.mk_div(lhs1, rhs), m);
        t = a.mk_div(lhs, rhs1);
    }
    ENSURE(!a.is_extended_numeral(t, n));
    {
        expr_ref lhs(a.mk_real(1), m);
        expr_ref lhs1(a.mk_real(1), m);
        expr_ref rhs(a.mk_real(-1), m);
        expr_ref rhs1(a.mk_add(lhs1, rhs), m);
        t = a.mk_div(lhs, rhs1);
    }
    ENSURE(!a.is_extended_numeral(t, n));
    {
        expr_ref lhs(a.mk_real(2), m);
        expr_ref rhs(a.mk_real(3), m);
        expr_ref lhs1(a.mk_mul(lhs, rhs), m);
        expr_ref lhs2(a.mk_real(1), m);
        expr_ref rhs1(a.mk_real(2), m);
        expr_ref rhs2(a.mk_add(lhs2, rhs1), m);
        t = a.mk_sub(lhs1, rhs2);
    }
    ENSURE(a.is_extended_numeral(t, n) && n == 3);
    t = a.mk_uminus(m.mk_const(symbol("x"), a.mk_real()));
    ENSURE(!a.is_extended_numeral(t, n));

    // A numeral under many wrappers must not overflow the stack.
    t = a.mk_real(1);
    for (unsigned i = 0; i < 200000; ++i)
        t = a.mk_uminus(t);
    ENSURE(a.is_extended_numeral(t, n) && n == 1);
    for (unsigned i = 0; i < 20000; ++i)
        t = a.mk_div(t, a.mk_real(1));
    ENSURE(a.is_extended_numeral(t, n) && n == 1);
    t = a.mk_real(1);
    for (unsigned i = 0; i < 20000; ++i) {
        expr_ref lhs(a.mk_add(t, a.mk_real(0)), m);
        expr_ref rhs(a.mk_real(1), m);
        t = a.mk_div(lhs, rhs);
    }
    ENSURE(a.is_extended_numeral(t, n) && n == 1);
    for (unsigned i = 0; i < 20000; ++i)
        t = a.mk_to_real(a.mk_to_int(t));
    ENSURE(a.is_extended_numeral(t, n) && n == 1);

    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref_vector lits(m);
    {
        expr_ref lhs(a.mk_mul(t, x), m);
        expr_ref rhs(a.mk_real(1), m);
        lits.push_back(a.mk_ge(lhs, rhs));
    }
    lits.push_back(a.mk_le(x, a.mk_real(0)));
    arith::theory_checker checker(m);
    ENSURE(checker.check(mk_farkas(m, ints(m, {1, 1}), lits)));
}

void tst_proof_replay() {
    tst_is_extended_numeral();
    tst_checker_nary_mul();
    tst_checker_printed_numerals();
    tst_replay_folds_printed_numerals();
}
