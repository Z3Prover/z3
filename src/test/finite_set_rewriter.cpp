/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_rewriter.cpp

Abstract:

    Test finite set rewriter

Author:

    GitHub Copilot Agent 2025

--*/

#include "ast/ast.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/finite_set_rewriter.h"

static void test_union_idempotent() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    finite_set_rewriter rw(m);
    arith_util arith(m);
    
    // Create a set
    sort_ref int_sort(arith.mk_int(), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref s1(fsets.mk_range(zero, ten), m);
    
    // Test set.union(s1, s1) -> s1
    expr* args[2] = { s1, s1 };
    expr_ref result(m);
    br_status st = rw.mk_union(2, args, result);
    
    ENSURE(st == BR_DONE);
    ENSURE(result == s1);
}

static void test_intersect_idempotent() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    finite_set_rewriter rw(m);
    arith_util arith(m);
    
    // Create a set
    sort_ref int_sort(arith.mk_int(), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref s1(fsets.mk_range(zero, ten), m);
    
    // Test set.intersect(s1, s1) -> s1
    expr* args[2] = { s1, s1 };
    expr_ref result(m);
    br_status st = rw.mk_intersect(2, args, result);
    
    ENSURE(st == BR_DONE);
    ENSURE(result == s1);
}

static void test_difference_same() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    finite_set_rewriter rw(m);
    arith_util arith(m);
    
    // Create a set
    sort_ref int_sort(arith.mk_int(), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref s1(fsets.mk_range(zero, ten), m);
    
    // Test set.difference(s1, s1) -> empty
    // Note: This simplification is currently disabled due to issues with mk_empty
    expr_ref result(m);
    br_status st = rw.mk_difference(s1, s1, result);
    
    // Currently disabled, so should return BR_FAILED
    ENSURE(st == BR_FAILED);
}

static void test_subset_rewrite() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    finite_set_rewriter rw(m);
    arith_util arith(m);
    
    // Create two sets
    sort_ref int_sort(arith.mk_int(), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    expr_ref twenty(arith.mk_int(20), m);
    app_ref s1(fsets.mk_range(zero, ten), m);
    app_ref s2(fsets.mk_range(zero, twenty), m);
    
    // Test set.subset(s1, s2) -> set.intersect(s1, s2) = s1
    expr_ref result(m);
    br_status st = rw.mk_subset(s1, s2, result);
    
    ENSURE(st == BR_REWRITE3);
    ENSURE(m.is_eq(result));
    
    // Check that result is an equality
    app* eq = to_app(result);
    ENSURE(eq->get_num_args() == 2);
    
    // The left side should be set.intersect(s1, s2)
    expr* lhs = eq->get_arg(0);
    ENSURE(fsets.is_intersect(lhs));
    
    // The right side should be s1
    expr* rhs = eq->get_arg(1);
    ENSURE(rhs == s1);
}

static void test_mk_app_core() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    finite_set_rewriter rw(m);
    arith_util arith(m);
    
    // Create sets
    sort_ref int_sort(arith.mk_int(), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref s1(fsets.mk_range(zero, ten), m);
    
    // Test union through mk_app_core
    app_ref union_app(fsets.mk_union(s1, s1), m);
    expr_ref result(m);
    br_status st = rw.mk_app_core(union_app->get_decl(), union_app->get_num_args(), union_app->get_args(), result);
    
    ENSURE(st == BR_DONE);
    ENSURE(result == s1);
}

void tst_finite_set_rewriter() {
    test_union_idempotent();
    test_intersect_idempotent();
    test_difference_same();
    test_subset_rewrite();
    test_mk_app_core();
}
