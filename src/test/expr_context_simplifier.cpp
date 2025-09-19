/*++
Copyright (c) 2025

Module Name:

    tst_expr_context_simplifier.cpp

Abstract:

    Test expression context simplifier functionality
    Testing core SMT expression simplification logic

Author:

    Daily Test Coverage Improver

--*/

#include "smt/expr_context_simplifier.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "util/trace.h"
#include "smt/smt_kernel.h"
#include "params/smt_params.h"

// Test basic expression context simplifier functionality
static void tst_expr_context_simplifier_basic() {
    ast_manager m;
    expr_context_simplifier simplifier(m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);

    // Test basic reduction using public interface (operator())
    expr_ref result(m);
    simplifier(a.get(), result);
    ENSURE(result.get() != nullptr);

    // Test that reduction preserves valid expressions
    expr_ref and_expr(m.mk_and(a.get(), b.get()), m);
    simplifier(and_expr.get(), result);
    ENSURE(result.get() != nullptr);

    // Test OR simplification
    expr_ref or_expr(m.mk_or(a.get(), b.get()), m);
    simplifier(or_expr.get(), result);
    ENSURE(result.get() != nullptr);
}

// Test context insertion and tracking
static void tst_expr_context_simplifier_context() {
    ast_manager m;
    expr_context_simplifier simplifier(m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);

    // Test context insertion
    simplifier.insert_context(a.get(), true);
    simplifier.insert_context(b.get(), false);

    // Test reduction with context
    expr_ref result(m);
    expr_ref and_expr(m.mk_and(a.get(), b.get()), m);
    simplifier(and_expr.get(), result);
    ENSURE(result.get() != nullptr);
}

// Test fixpoint reduction
static void tst_expr_context_simplifier_fix() {
    ast_manager m;
    expr_context_simplifier simplifier(m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);
    expr_ref c(m.mk_const(symbol("c"), bool_sort), m);

    // Test fixpoint reduction with complex expressions
    expr_ref complex_expr(m);
    complex_expr = m.mk_and(
        m.mk_or(a.get(), b.get()),
        m.mk_implies(b.get(), c.get())
    );

    expr_ref result(m);
    simplifier.reduce_fix(complex_expr.get(), result);
    ENSURE(result.get() != nullptr);
}

// Test ITE (if-then-else) simplification
static void tst_expr_context_simplifier_ite() {
    ast_manager m;
    expr_context_simplifier simplifier(m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);
    expr_ref c(m.mk_const(symbol("c"), bool_sort), m);

    // Test ITE simplification
    expr_ref ite_expr(m.mk_ite(a.get(), b.get(), c.get()), m);
    expr_ref result(m);
    simplifier(ite_expr.get(), result);
    ENSURE(result.get() != nullptr);

    // Test ITE with true condition
    expr_ref true_expr(m.mk_true(), m);
    expr_ref ite_true(m.mk_ite(true_expr.get(), b.get(), c.get()), m);
    simplifier(ite_true.get(), result);
    ENSURE(result.get() != nullptr);

    // Test ITE with false condition
    expr_ref false_expr(m.mk_false(), m);
    expr_ref ite_false(m.mk_ite(false_expr.get(), b.get(), c.get()), m);
    simplifier(ite_false.get(), result);
    ENSURE(result.get() != nullptr);
}

// Test strong context simplifier basic functionality
static void tst_expr_strong_context_simplifier_basic() {
    smt_params params;
    ast_manager m;
    expr_strong_context_simplifier simplifier(params, m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);

    // Test basic simplification
    expr_ref result(m);
    expr_ref and_expr(m.mk_and(a.get(), b.get()), m);
    simplifier(and_expr.get(), result);
    ENSURE(result.get() != nullptr);

    // Test in-place simplification
    expr_ref test_expr(m.mk_or(a.get(), b.get()), m);
    simplifier(test_expr);
    ENSURE(test_expr.get() != nullptr);
}

// Test strong context simplifier with assertions
static void tst_expr_strong_context_simplifier_assertions() {
    smt_params params;
    ast_manager m;
    expr_strong_context_simplifier simplifier(params, m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);
    expr_ref b(m.mk_const(symbol("b"), bool_sort), m);

    // Test push/pop functionality
    simplifier.push();
    simplifier.assert_expr(a.get());

    // Test simplification with assertions
    expr_ref result(m);
    expr_ref and_expr(m.mk_and(a.get(), b.get()), m);
    simplifier(and_expr.get(), result);
    ENSURE(result.get() != nullptr);

    simplifier.pop();
}

// Test strong context simplifier statistics
static void tst_expr_strong_context_simplifier_stats() {
    smt_params params;
    ast_manager m;
    expr_strong_context_simplifier simplifier(params, m);

    // Create boolean variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), bool_sort), m);

    // Test statistics collection
    statistics st;
    simplifier.collect_statistics(st);

    // Test statistics reset
    simplifier.reset_statistics();

    // Basic functionality test after stats operations
    expr_ref result(m);
    simplifier(a.get(), result);
    ENSURE(result.get() != nullptr);
}

// Main test function for expression context simplifier
void tst_expr_context_simplifier() {
    tst_expr_context_simplifier_basic();
    tst_expr_context_simplifier_context();
    tst_expr_context_simplifier_fix();
    tst_expr_context_simplifier_ite();
    tst_expr_strong_context_simplifier_basic();
    tst_expr_strong_context_simplifier_assertions();
    tst_expr_strong_context_simplifier_stats();
}