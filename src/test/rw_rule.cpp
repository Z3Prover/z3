/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    rw_rule.cpp  (test)

Abstract:

    Tests for the rw_rule abstract machine and rw_evaluator.

Author:

    Copilot 2026

Notes:

--*/

#include "ast/rewriter/rw_rule.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include <iostream>

// Helper: print a test result and assert the expected condition.
static void check(ast_manager & m, const char * label, expr * result, expr * expected) {
    bool ok = (result == expected);
    std::cout << label << ": " << mk_pp(result, m)
              << (ok ? "  [OK]" : "  [FAIL]") << "\n";
    ENSURE(ok);
}

static void check_true(ast_manager & m, const char * label, expr * result) {
    check(m, label, result, m.mk_true());
}

static void check_false(ast_manager & m, const char * label, expr * result) {
    check(m, label, result, m.mk_false());
}

// ---------------------------------------------------------------------------
// Arithmetic tests
// ---------------------------------------------------------------------------

static void test_arith_add_identity() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref y(m.mk_const(symbol("y"), real_sort), m);

    // 0 + x -> x  (Int)
    ev(arith.mk_add(arith.mk_int(0), x), result);
    check(m, "0_i + x", result, x);

    // x + 0 -> x  (Int)
    ev(arith.mk_add(x, arith.mk_int(0)), result);
    check(m, "x + 0_i", result, x);

    // 0 + y -> y  (Real)
    ev(arith.mk_add(arith.mk_real(0), y), result);
    check(m, "0_r + y", result, y);

    // y + 0 -> y  (Real)
    ev(arith.mk_add(y, arith.mk_real(0)), result);
    check(m, "y + 0_r", result, y);
}

static void test_arith_mul_identity() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref y(m.mk_const(symbol("y"), real_sort), m);

    // 1 * x -> x  (Int)
    ev(arith.mk_mul(arith.mk_int(1), x), result);
    check(m, "1_i * x", result, x);

    // x * 1 -> x  (Int)
    ev(arith.mk_mul(x, arith.mk_int(1)), result);
    check(m, "x * 1_i", result, x);

    // 1 * y -> y  (Real)
    ev(arith.mk_mul(arith.mk_real(1), y), result);
    check(m, "1_r * y", result, y);

    // y * 1 -> y  (Real)
    ev(arith.mk_mul(y, arith.mk_real(1)), result);
    check(m, "y * 1_r", result, y);
}

static void test_arith_mul_zero() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref y(m.mk_const(symbol("y"), real_sort), m);

    expr_ref zero_i(arith.mk_int(0),  m);
    expr_ref zero_r(arith.mk_real(0), m);

    // 0 * x -> 0  (Int)
    ev(arith.mk_mul(zero_i, x), result);
    ENSURE(arith.is_numeral(result) && arith.is_zero(result) && arith.is_int(result));

    // x * 0 -> 0  (Int)
    ev(arith.mk_mul(x, zero_i), result);
    ENSURE(arith.is_numeral(result) && arith.is_zero(result) && arith.is_int(result));

    // 0 * y -> 0  (Real)
    ev(arith.mk_mul(zero_r, y), result);
    ENSURE(arith.is_numeral(result) && arith.is_zero(result) && !arith.is_int(result));

    // y * 0 -> 0  (Real)
    ev(arith.mk_mul(y, zero_r), result);
    ENSURE(arith.is_numeral(result) && arith.is_zero(result) && !arith.is_int(result));

    std::cout << "mul-zero tests: [OK]\n";
}

static void test_arith_sub_zero() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref y(m.mk_const(symbol("y"), real_sort), m);

    // x - 0 -> x  (Int)
    ev(arith.mk_sub(x, arith.mk_int(0)), result);
    check(m, "x - 0_i", result, x);

    // y - 0 -> y  (Real)
    ev(arith.mk_sub(y, arith.mk_real(0)), result);
    check(m, "y - 0_r", result, y);
}

static void test_arith_uminus() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref y(m.mk_const(symbol("y"), real_sort), m);

    // -(-x) -> x  (Int)
    ev(arith.mk_uminus(arith.mk_uminus(x)), result);
    check(m, "-(-x)_i", result, x);

    // -(-y) -> y  (Real)
    ev(arith.mk_uminus(arith.mk_uminus(y)), result);
    check(m, "-(-y)_r", result, y);
}

// ---------------------------------------------------------------------------
// Boolean tests
// ---------------------------------------------------------------------------

static void test_bool_and() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref bx(m.mk_const(symbol("bx"), bool_sort), m);

    // true /\ x -> x
    ev(m.mk_and(m.mk_true(), bx), result);
    check(m, "true /\\ x", result, bx);

    // x /\ true -> x
    ev(m.mk_and(bx, m.mk_true()), result);
    check(m, "x /\\ true", result, bx);

    // false /\ x -> false
    ev(m.mk_and(m.mk_false(), bx), result);
    check_false(m, "false /\\ x", result);

    // x /\ false -> false
    ev(m.mk_and(bx, m.mk_false()), result);
    check_false(m, "x /\\ false", result);
}

static void test_bool_or() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref bx(m.mk_const(symbol("bx"), bool_sort), m);

    // false \/ x -> x
    ev(m.mk_or(m.mk_false(), bx), result);
    check(m, "false \\/ x", result, bx);

    // x \/ false -> x
    ev(m.mk_or(bx, m.mk_false()), result);
    check(m, "x \\/ false", result, bx);

    // true \/ x -> true
    ev(m.mk_or(m.mk_true(), bx), result);
    check_true(m, "true \\/ x", result);

    // x \/ true -> true
    ev(m.mk_or(bx, m.mk_true()), result);
    check_true(m, "x \\/ true", result);
}

static void test_bool_not() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref bx(m.mk_const(symbol("bx"), bool_sort), m);

    // not(not(x)) -> x
    ev(m.mk_not(m.mk_not(bx)), result);
    check(m, "not(not(x))", result, bx);

    // not(true) -> false
    ev(m.mk_not(m.mk_true()), result);
    check_false(m, "not(true)", result);

    // not(false) -> true
    ev(m.mk_not(m.mk_false()), result);
    check_true(m, "not(false)", result);
}

// ---------------------------------------------------------------------------
// ITE tests
// ---------------------------------------------------------------------------

static void test_ite() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * bool_sort = m.mk_bool_sort();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref y(m.mk_const(symbol("y"), int_sort),  m);
    expr_ref c(m.mk_const(symbol("c"), bool_sort), m);

    // ite(true, x, y) -> x
    ev(m.mk_ite(m.mk_true(), x, y), result);
    check(m, "ite(true,x,y)", result, x);

    // ite(false, x, y) -> y
    ev(m.mk_ite(m.mk_false(), x, y), result);
    check(m, "ite(false,x,y)", result, y);

    // ite(c, x, x) -> x
    ev(m.mk_ite(c, x, x), result);
    check(m, "ite(c,x,x)", result, x);
}

// ---------------------------------------------------------------------------
// Equality tests
// ---------------------------------------------------------------------------

static void test_eq_reflexivity() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * bool_sort = m.mk_bool_sort();

    expr_ref x(m.mk_const(symbol("x"), int_sort),  m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);

    // x = x -> true  (Int)
    ev(m.mk_eq(x, x), result);
    check_true(m, "x = x (Int)", result);

    // b = b -> true  (Bool)
    ev(m.mk_eq(b, b), result);
    check_true(m, "b = b (Bool)", result);
}

// ---------------------------------------------------------------------------
// Compound rewriting: verify multi-level simplification
// ---------------------------------------------------------------------------

static void test_compound() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort = arith.mk_int();
    expr_ref x(m.mk_const(symbol("x"), int_sort), m);

    // (0 + x) + (1 * x)  should simplify to  x + x
    expr_ref lhs(arith.mk_add(arith.mk_int(0), x), m);
    expr_ref rhs(arith.mk_mul(arith.mk_int(1), x), m);
    expr_ref term(arith.mk_add(lhs, rhs), m);
    ev(term, result);
    // Both sub-terms simplify: result should be x + x
    expr_ref expected(arith.mk_add(x, x), m);
    check(m, "(0+x)+(1*x)", result, expected);
}

// ---------------------------------------------------------------------------
// New rules: Bool idempotency, complementation, eq simplification, ITE Bool
// ---------------------------------------------------------------------------

static void test_bool_idempotency() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref bx(m.mk_const(symbol("bx"), bool_sort), m);

    // x /\ x -> x
    ev(m.mk_and(bx, bx), result);
    check(m, "x /\\ x", result, bx);

    // x \/ x -> x
    ev(m.mk_or(bx, bx), result);
    check(m, "x \\/ x", result, bx);
}

static void test_bool_complementation() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref bx(m.mk_const(symbol("bx"), bool_sort), m);

    // x /\ not(x) -> false
    ev(m.mk_and(bx, m.mk_not(bx)), result);
    check_false(m, "x /\\ not(x)", result);

    // not(x) /\ x -> false
    ev(m.mk_and(m.mk_not(bx), bx), result);
    check_false(m, "not(x) /\\ x", result);

    // x \/ not(x) -> true
    ev(m.mk_or(bx, m.mk_not(bx)), result);
    check_true(m, "x \\/ not(x)", result);

    // not(x) \/ x -> true
    ev(m.mk_or(m.mk_not(bx), bx), result);
    check_true(m, "not(x) \\/ x", result);
}

static void test_bool_eq_simplification() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref bx(m.mk_const(symbol("bx"), bool_sort), m);

    // (= true x) -> x
    ev(m.mk_eq(m.mk_true(), bx), result);
    check(m, "(= true bx)", result, bx);

    // (= x true) -> x
    ev(m.mk_eq(bx, m.mk_true()), result);
    check(m, "(= bx true)", result, bx);

    // (= false x) -> not(x)
    ev(m.mk_eq(m.mk_false(), bx), result);
    {
        expr_ref not_bx(m.mk_not(bx), m);
        check(m, "(= false bx)", result, not_bx);
    }

    // (= x false) -> not(x)
    ev(m.mk_eq(bx, m.mk_false()), result);
    {
        expr_ref not_bx(m.mk_not(bx), m);
        check(m, "(= bx false)", result, not_bx);
    }
}

static void test_ite_bool_special() {
    ast_manager m;
    reg_decl_plugins(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * bool_sort = m.mk_bool_sort();
    expr_ref c(m.mk_const(symbol("c"), bool_sort), m);

    // ite(c, true, false) -> c
    ev(m.mk_ite(c, m.mk_true(), m.mk_false()), result);
    check(m, "ite(c,true,false)", result, c);

    // ite(c, false, true) -> not(c)
    ev(m.mk_ite(c, m.mk_false(), m.mk_true()), result);
    {
        expr_ref not_c(m.mk_not(c), m);
        check(m, "ite(c,false,true)", result, not_c);
    }
}

static void test_arith_div_mod() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort = arith.mk_int();
    expr_ref x(m.mk_const(symbol("x"), int_sort), m);

    // idiv(x, 1) -> x
    ev(arith.mk_idiv(x, arith.mk_int(1)), result);
    check(m, "x div 1", result, x);

    // mod(x, 1) -> 0
    ev(arith.mk_mod(x, arith.mk_int(1)), result);
    ENSURE(arith.is_zero(result));
    std::cout << "x mod 1: " << mk_pp(result, m) << "  [OK]\n";

    // rem(x, 1) -> 0
    ev(arith.mk_rem(x, arith.mk_int(1)), result);
    ENSURE(arith.is_zero(result));
    std::cout << "x rem 1: " << mk_pp(result, m) << "  [OK]\n";
}

static void test_arith_uminus_zero() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    // -(0_i) -> 0_i
    ev(arith.mk_uminus(arith.mk_int(0)), result);
    ENSURE(arith.is_zero(result) && arith.is_int(result));
    std::cout << "-(0_i): " << mk_pp(result, m) << "  [OK]\n";

    // -(0_r) -> 0_r
    ev(arith.mk_uminus(arith.mk_real(0)), result);
    ENSURE(arith.is_zero(result) && !arith.is_int(result));
    std::cout << "-(0_r): " << mk_pp(result, m) << "  [OK]\n";
}

static void test_arith_le_ge_reflexivity() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_evaluator ev(m);
    expr_ref result(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();
    expr_ref xi(m.mk_const(symbol("xi"), int_sort),  m);
    expr_ref xr(m.mk_const(symbol("xr"), real_sort), m);

    // xi <= xi -> true
    ev(arith.mk_le(xi, xi), result);
    check_true(m, "xi <= xi", result);

    // xi >= xi -> true
    ev(arith.mk_ge(xi, xi), result);
    check_true(m, "xi >= xi", result);

    // xr <= xr -> true
    ev(arith.mk_le(xr, xr), result);
    check_true(m, "xr <= xr", result);

    // xr >= xr -> true
    ev(arith.mk_ge(xr, xr), result);
    check_true(m, "xr >= xr", result);
}

// ---------------------------------------------------------------------------
// Direct rw_table API test (no evaluator)
// ---------------------------------------------------------------------------

static void test_table_direct() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);

    rw_table table(m);
    table.populate_rules();

    expr_ref result(m);
    proof_ref pr(m);

    sort * int_sort = arith.mk_int();
    expr_ref x(m.mk_const(symbol("x"), int_sort), m);

    // Directly call reduce_app for  0 + x
    expr * args[2] = { arith.mk_int(0), x };
    func_decl * add_decl = arith.mk_add(arith.mk_int(0), x)->get_decl();
    br_status st = table.reduce_app(add_decl, 2, args, result, pr);

    std::cout << "table.reduce_app(0+x): status=" << st
              << " result=" << mk_pp(result, m) << "\n";
    ENSURE(st == BR_DONE);
    ENSURE(result.get() == x.get());
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

void tst_rw_rule() {
    std::cout << "=== rw_rule tests ===\n";
    test_arith_add_identity();
    test_arith_mul_identity();
    test_arith_mul_zero();
    test_arith_sub_zero();
    test_arith_uminus();
    test_bool_and();
    test_bool_or();
    test_bool_not();
    test_ite();
    test_eq_reflexivity();
    test_compound();
    test_table_direct();
    // new-rule tests
    test_bool_idempotency();
    test_bool_complementation();
    test_bool_eq_simplification();
    test_ite_bool_special();
    test_arith_div_mod();
    test_arith_uminus_zero();
    test_arith_le_ge_reflexivity();
    std::cout << "=== rw_rule: all tests passed ===\n";
}
