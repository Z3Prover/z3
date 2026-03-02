/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    nseq_basic.cpp

Abstract:

    Basic unit tests for the Nielsen-based string theory solver (theory_nseq).
    Tests that theory_nseq can be selected via smt.string_solver=nseq and
    correctly handles basic string constraints.

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/

#include "api/z3.h"
#include <iostream>
#include "util/util.h"

// Helper: create a Z3 context with string_solver set to nseq
static Z3_context mk_nseq_ctx() {
    Z3_global_param_set("smt.string_solver", "nseq");
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_global_param_reset_all();
    return ctx;
}

// Test 1: Simple string constant equality (sat)
static void test_nseq_simple_sat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast hello = Z3_mk_string(ctx, "hello");
    Z3_ast eq = Z3_mk_eq(ctx, x, hello);
    Z3_solver_assert(ctx, s, eq);
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 2: Simple string constant disequality (unsat)
static void test_nseq_simple_unsat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast hello = Z3_mk_string(ctx, "hello");
    Z3_ast world = Z3_mk_string(ctx, "world");
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, hello));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, world));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_FALSE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 3: String concatenation (sat)
static void test_nseq_concat_sat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), str_sort);
    Z3_ast hello = Z3_mk_string(ctx, "hello");
    Z3_ast args[2] = { x, y };
    Z3_ast xy = Z3_mk_seq_concat(ctx, 2, args);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xy, hello));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 4: Prefix constraint (sat)
static void test_nseq_prefix_sat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast pre = Z3_mk_string(ctx, "hel");
    // prefix("hel", x)
    Z3_ast prefix_cond = Z3_mk_seq_prefix(ctx, pre, x);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
    Z3_ast len_x = Z3_mk_seq_length(ctx, x);
    Z3_solver_assert(ctx, s, prefix_cond);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, len_x, five));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 5: Empty string equality (sat)
static void test_nseq_empty_sat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast empty = Z3_mk_string(ctx, "");
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, empty));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 6: Basic regex membership (sat)
static void test_nseq_regex_sat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    // x = "abab" ∧ x ∈ (ab)*
    Z3_ast abab = Z3_mk_string(ctx, "abab");
    Z3_ast ab_re = Z3_mk_seq_to_re(ctx, Z3_mk_string(ctx, "ab"));
    Z3_ast star_re = Z3_mk_re_star(ctx, ab_re);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, abab));
    Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, star_re));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 7: Basic regex membership (unsat)
static void test_nseq_regex_unsat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    // x = "abc" ∧ x ∈ (ab)*  → unsat ("abc" is not in (ab)*)
    Z3_ast abc = Z3_mk_string(ctx, "abc");
    Z3_ast ab_re = Z3_mk_seq_to_re(ctx, Z3_mk_string(ctx, "ab"));
    Z3_ast star_re = Z3_mk_re_star(ctx, ab_re);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, abc));
    Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, star_re));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_FALSE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Test 8: Length constraint (sat)
static void test_nseq_length_sat() {
    Z3_context ctx = mk_nseq_ctx();
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort str_sort = Z3_mk_string_sort(ctx);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), str_sort);
    Z3_ast len_x = Z3_mk_seq_length(ctx, x);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, len_x, three));
    Z3_lbool r = Z3_solver_check(ctx, s);
    ENSURE(r == Z3_L_TRUE);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

void tst_nseq_basic() {
    test_nseq_simple_sat();
    test_nseq_simple_unsat();
    test_nseq_concat_sat();
    test_nseq_prefix_sat();
    test_nseq_empty_sat();
    test_nseq_regex_sat();
    test_nseq_regex_unsat();
    test_nseq_length_sat();
    std::cout << "nseq_basic: all tests passed\n";
}
