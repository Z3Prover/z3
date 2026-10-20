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
#include "sat/sat_proof_trim.h"
#include "sat/smt/arith_theory_checker.h"
#include "sat/smt/tseitin_theory_checker.h"
#include <cstdlib>
#include <iostream>
#include <sstream>

// The replay frontend calls exit(0) when a step does not verify. That would end
// the test binary successfully with the remaining checks unrun; turn it into a
// failure instead.
static bool g_replaying = false;
static std::ostringstream* g_captured = nullptr;

static void replay_exit_guard() {
    if (!g_replaying)
        return;
    std::cerr << "proof replay exited before completing:\n" << g_captured->str();
    std::_Exit(1);
}

struct scoped_replay {
    std::streambuf* saved;
    scoped_replay(std::ostringstream& captured) : saved(std::cout.rdbuf(captured.rdbuf())) {
        g_captured = &captured;
        g_replaying = true;
    }
    ~scoped_replay() {
        std::cout.rdbuf(saved);
        g_replaying = false;
        g_captured = nullptr;
    }
};

// Replay a clause proof log and return what the checker printed.
static std::string replay(char const* log) {
    static int const registered = std::atexit(replay_exit_guard);
    ENSURE(registered == 0);
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context ctx(false, &m);
    install_proof_cmds(ctx);
    std::istringstream is(log);
    std::ostringstream captured;
    bool ok;
    {
        scoped_replay scope(captured);
        ok = parse_smt2_commands(ctx, is);
    }
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

static app_ref mk_arith_hint(ast_manager &m, char const *name, expr_ref_vector const &coeffs,
                             expr_ref_vector const &lits) {
    ENSURE(coeffs.size() == lits.size());
    expr_ref_vector args(m);
    for (unsigned i = 0; i < lits.size(); ++i) {
        args.push_back(coeffs.get(i));
        args.push_back(lits.get(i));
    }
    return app_ref(m.mk_app(symbol(name), args.size(), args.data(), m.mk_proof_sort()), m);
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
    ENSURE(checker.check(mk_arith_hint(m, "farkas", ints(m, {1, 6}), lits)));
    // x * y is nonlinear; the product stays one opaque term and the hint is not proven.
    lits = parse_lits(m,
        "(declare-const x Real)(declare-const y Real)"
        "(assert (>= (* 2.0 x y) 1.0))(assert (<= x 0.0))");
    ENSURE(!checker.check(mk_arith_hint(m, "farkas", ints(m, {1, 2}), lits)));
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
    ENSURE(checker.check(mk_arith_hint(m, "farkas", coeffs, lits)));
}

static void tst_checker_zero_weight_strictness() {
    ast_manager m;
    reg_decl_plugins(m);
    arith::theory_checker checker(m);
    for (char const *atom : {"(< x 0)", "(> x 0)", "(not (<= x 0))", "(not (>= x 0))"}) {
        std::string source = std::string("(declare-const x Real)(assert ") + atom + ")";
        auto lits = parse_lits(m, source.c_str());
        ENSURE(!checker.check(mk_arith_hint(m, "farkas", ints(m, {0}), lits)));
        lits.push_back(mk_not(m, lits.get(0)));
        ENSURE(checker.check(mk_arith_hint(m, "farkas", ints(m, {1, 1}), lits)));
    }

    auto lits = parse_lits(m, "(declare-const x Real)(declare-const y Real)"
                              "(assert (< x 0))(assert (<= y 0))(assert (>= y 0))");
    for (char const *name : {"farkas", "bound"})
        ENSURE(!checker.check(mk_arith_hint(m, name, ints(m, {0, 1, 1}), lits)));

    // A zero-weight premise must not discard a genuine strict contradiction.
    lits = parse_lits(m, "(declare-const x Real)(declare-const y Real)"
                         "(assert (< x 0))(assert (< y 0))(assert (>= y 0))");
    for (char const *name : {"farkas", "bound"})
        ENSURE(checker.check(mk_arith_hint(m, name, ints(m, {0, 1, 1}), lits)));

    lits = parse_lits(m, "(declare-const x Real)(assert (<= x 1))(assert (> x 0))");
    ENSURE(!checker.check(mk_arith_hint(m, "bound", ints(m, {1, 0}), lits)));
}

static void tst_checker_bound_row_strictness() {
    ast_manager m;
    reg_decl_plugins(m);
    arith::theory_checker checker(m);
    // Both literals hold at x = -1. The premise's strictness cannot make
    // the separate consequent row 0 <= 0 contradictory.
    auto lits = parse_lits(m, "(declare-const x Real)"
                              "(assert (< x 0))(assert (<= (- x x) 0))");
    ENSURE(!checker.check(mk_arith_hint(m, "bound", ints(m, {1, 1}), lits)));

    lits = parse_lits(m, "(declare-const x Real)"
                         "(assert (< x 0))(assert (not (<= (- x x) 0)))");
    ENSURE(checker.check(mk_arith_hint(m, "bound", ints(m, {1, 1}), lits)));

    lits = parse_lits(m, "(declare-const x Real)"
                         "(assert (< (- x x) 0))(assert (<= (- x x) 0))");
    ENSURE(checker.check(mk_arith_hint(m, "bound", ints(m, {1, 1}), lits)));

    // Combining rows must retain strictness from either participating row.
    for (char const *source : {"(declare-const x Real)(assert (< x 0))(assert (>= x 0))",
                               "(declare-const x Real)(assert (<= x 0))(assert (> x 0))",
                               "(declare-const x Real)(declare-const y Real)"
                               "(assert (= x y))(assert (< x 0))(assert (>= y 0))"}) {
        lits = parse_lits(m, source);
        auto coeffs = lits.size() == 2 ? ints(m, {1, 1}) : ints(m, {1, 1, 1});
        for (char const *name : {"farkas", "bound"})
            ENSURE(checker.check(mk_arith_hint(m, name, coeffs, lits)));
    }
}

static void tst_checker_implied_eq_conclusion() {
    ast_manager m;
    reg_decl_plugins(m);
    arith::theory_checker checker(m);
    for (char const *sort : {"Real", "Int"}) {
        std::string decls = std::string("(declare-const x ") + sort + ")(declare-const y " + sort + ")";
        auto lits = parse_lits(m, (decls + "(assert (not (= x y)))").c_str());
        ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {0}), lits)));
        ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1}), lits)));

        lits = parse_lits(m, (decls + "(assert (<= x 0))").c_str());
        ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1}), lits)));
        lits = parse_lits(m, (decls + "(assert (= x y))").c_str());
        ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1}), lits)));

        lits = parse_lits(m, (decls + "(assert (<= x y))(assert (>= x y))(assert (not (= x y)))").c_str());
        for (int coeff : {1, -1})
            ENSURE(checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, coeff}), lits)));
        ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, 0}), lits)));
    }

    expr_ref_vector empty(m);
    ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", empty, empty)));
    auto args = ints(m, {1});
    app_ref incomplete(m.mk_app(symbol("implied-eq"), args.size(), args.data(), m.mk_proof_sort()), m);
    ENSURE(!checker.check(incomplete));
}

static void tst_checker_implied_eq_constant_rows() {
    ast_manager m;
    reg_decl_plugins(m);
    arith::theory_checker checker(m);
    for (char const *sort : {"Real", "Int"}) {
        std::string decls = std::string("(declare-const x ") + sort + ")(declare-const y " + sort +
                           ")(declare-const z " + sort + ")";
        for (char const *tautology : {"(<= 0 1)", "(< 0 1)", "(<= 0 0)"}) {
            std::string premise = decls + "(assert " + tautology + ")";
            auto lits = parse_lits(m, (premise + "(assert (<= x y))(assert (>= x y))"
                                               "(assert (not (= x y)))").c_str());
            ENSURE(checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, 1, 1}), lits)));

            lits = parse_lits(m, (premise + "(assert (not (= x y)))").c_str());
            ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1}), lits)));
        }

        // Equality substitution and elimination can also leave constant rows.
        auto lits = parse_lits(m, (decls + "(assert (= z 0))(assert (<= z 1))"
                                         "(assert (<= x y))(assert (>= x y))(assert (not (= x y)))").c_str());
        ENSURE(checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, 1, 1, 1}), lits)));
        lits = parse_lits(m, (decls + "(assert (<= z 1))(assert (>= z 0))"
                                    "(assert (<= x y))(assert (>= x y))(assert (not (= x y)))").c_str());
        ENSURE(checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, 1, 1, 1}), lits)));

        for (char const *contradiction : {"(<= 1 0)", "(< 0 0)"}) {
            lits = parse_lits(m, (decls + "(assert (<= 0 0))(assert " + contradiction +
                                        ")(assert (not (= x y)))").c_str());
            ENSURE(checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, 1}), lits)));

            // An early contradiction must not leave tight rows for the next hint.
            lits = parse_lits(m, (decls + "(assert (not (= x y)))").c_str());
            ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1}), lits)));
        }
        lits = parse_lits(m, (decls + "(assert (<= z 0))(assert (>= z 1))"
                                    "(assert (not (= x y)))").c_str());
        ENSURE(checker.check(mk_arith_hint(m, "implied-eq", ints(m, {1, 1, 1}), lits)));

        lits = parse_lits(m, (decls + "(assert (< 0 0))(assert (not (= x y)))").c_str());
        ENSURE(!checker.check(mk_arith_hint(m, "implied-eq", ints(m, {0, 1}), lits)));
    }
}

static void tst_replay_implied_eq_constant_row() {
    check_verified_natively(replay(
        "(declare-const x Real)(declare-const y Real)"
        "(assume (<= 0.0 1.0))(assume (<= x y))(assume (>= x y))(assume (not (= x y)))"
        "(declare-fun implied-eq (Int Bool Int Bool Int Bool Int Bool) Proof)"
        "(infer (implied-eq 1 (<= 0.0 1.0) 1 (<= x y) 1 (>= x y) 1 (not (= x y))))"
        "(declare-fun rup () Proof)(infer rup)"), "implied-eq 1");
}

// A tseitin hint lists the gate clause itself.
static bool check_tseitin(ast_manager& m, expr_ref_vector const& lits) {
    app_ref hint(m.mk_app(symbol("tseitin"), lits.size(), lits.data(), m.mk_proof_sort()), m);
    tseitin::theory_checker checker(m);
    return checker.check(hint);
}

static bool check_tseitin(ast_manager& m, char const* source) {
    return check_tseitin(m, parse_lits(m, source));
}

// An xor gate clause is a tautology only when every argument of the xor is
// fixed by a clause literal and the xor then takes the value the clause needs:
// an odd number of true arguments for a positive gate literal, an even number
// for a negated one.
static void tst_checker_tseitin_xor() {
    ast_manager m;
    reg_decl_plugins(m);
    char const* decls = "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)";
    auto check = [&](char const* clause) {
        return check_tseitin(m, (std::string(decls) + clause).c_str());
    };
    // The four clauses defining (xor a b).
    ENSURE(check("(assert (xor a b))(assert a)(assert (not b))"));
    ENSURE(check("(assert (xor a b))(assert (not a))(assert b)"));
    ENSURE(check("(assert (not (xor a b)))(assert a)(assert b)"));
    ENSURE(check("(assert (not (xor a b)))(assert (not a))(assert (not b))"));
    // Each wrong-polarity clause has a falsifying assignment.
    ENSURE(!check("(assert (xor a b))(assert a)(assert b)"));
    ENSURE(!check("(assert (xor a b))(assert (not a))(assert (not b))"));
    ENSURE(!check("(assert (not (xor a b)))(assert a)(assert (not b))"));
    ENSURE(!check("(assert (not (xor a b)))(assert (not a))(assert b)"));
    // An argument the clause leaves free can take either value.
    ENSURE(!check("(assert (not (xor a b)))(assert a)"));
    ENSURE(!check("(assert (not (xor a b)))(assert (not a))"));
    ENSURE(!check("(assert (xor a b))(assert (not a))"));
    // Repeated and constant arguments.
    ENSURE(!check("(assert (xor a a))(assert a)"));
    ENSURE(!check("(assert (xor a a))(assert (not a))"));
    ENSURE(check("(assert (not (xor a a)))(assert a)"));
    ENSURE(check("(assert (xor a true))(assert a)"));
    ENSURE(!check("(assert (xor a true))(assert (not a))"));
    ENSURE(check("(assert (xor a false))(assert (not a))"));
    ENSURE(!check("(assert (xor a false))(assert a)"));
    // xor is binary in the AST, (xor a b c) is (xor a (xor b c)): the inner
    // gate is an argument the clause does not fix.
    ENSURE(!check("(assert (xor a b c))(assert a)(assert b)(assert (not c))"));
    ENSURE(check("(assert (xor a b c))(assert a)(assert (not (xor b c)))"));
    ENSURE(!check("(assert (xor a b c))(assert a)(assert (xor b c))"));
    // Other gates are unaffected.
    ENSURE(check("(assert (and a b))(assert (not a))(assert (not b))"));
    ENSURE(!check("(assert (and a b))(assert (not a))(assert b)"));
}

// Both polarities of the gate verify natively in a replayed log.
static void tst_replay_tseitin_xor() {
    check_verified_natively(replay(
        "(declare-fun a () Bool)(declare-fun b () Bool)(declare-fun p () Bool)"
        "(define-const $1 Bool (xor a b))"
        "(declare-fun tseitin (Bool Bool Bool) Proof)"
        "(infer (not a) (not b) (not $1) (tseitin (not $1) (not a) (not b)))"
        "(infer a b (not $1) (tseitin (not $1) a b))"
        "(infer a (not b) $1 (tseitin $1 a (not b)))"
        "(infer (not a) b $1 (tseitin $1 (not a) b))"
        "(assume p $1)(assume (not p))(assume a)(assume b)"
        "(declare-fun rup () Proof)(infer $1 rup)(infer rup)"), "tseitin 4");
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
    ENSURE(checker.check(mk_arith_hint(m, "farkas", ints(m, {1, 1}), lits)));
}

static void tst_trim_satisfied_clause() {
    params_ref params;
    reslimit limit;
    sat::proof_trim trim(params, limit);
    sat::literal p(trim.mk_var(), false), q(trim.mk_var(), false), r(trim.mk_var(), false);
    auto assume = [&](unsigned id, std::initializer_list<sat::literal> literals) {
        trim.init_clause();
        for (auto literal : literals)
            trim.add_literal(literal.var(), literal.sign());
        trim.assume(id);
    };
    assume(0, {p});
    assume(1, {~q});
    assume(2, {p, q, r}); // Already satisfied: it must not propagate r.
    assume(3, {~r});
    assume(4, {~p});
    trim.init_clause();
    trim.infer(5);
    auto core = trim.trim();
    ENSURE(core.size() == 3);
    ENSURE(core[0].first == 0);
    ENSURE(core[1].first == 4);
    ENSURE(core[2].first == 5);
}

void tst_proof_replay() {
    tst_trim_satisfied_clause();
    tst_is_extended_numeral();
    tst_checker_nary_mul();
    tst_checker_printed_numerals();
    tst_checker_zero_weight_strictness();
    tst_checker_bound_row_strictness();
    tst_checker_implied_eq_conclusion();
    tst_checker_implied_eq_constant_rows();
    tst_replay_implied_eq_constant_row();
    tst_checker_tseitin_xor();
    tst_replay_tseitin_xor();
    tst_replay_folds_printed_numerals();
}
