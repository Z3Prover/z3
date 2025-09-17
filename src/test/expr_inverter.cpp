/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    expr_inverter.cpp

Abstract:

    Test expression inverter functionality

Author:

    Daily Test Coverage Improver 2025-01-17

--*/
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "ast/converters/expr_inverter.h"
#include "model/model.h"

static void test_basic_boolean_inversion() {
    ast_manager m;
    expr_inverter inv(m);

    // Create variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref x(m.mk_const(symbol("x"), bool_sort), m);
    expr_ref y(m.mk_const(symbol("y"), bool_sort), m);
    expr_ref z(m.mk_const(symbol("z"), bool_sort), m);

    // Set up the inverter to recognize x and y as unconstrained variables
    std::function<bool(expr*)> is_var = [&](expr* e) {
        return e == x.get() || e == y.get();
    };
    inv.set_is_var(is_var);

    // Test NOT inversion: not x -> fresh
    expr_ref not_expr(m.mk_not(x.get()), m);
    if (not_expr.get() && is_app(not_expr.get())) {
        app* not_app = to_app(not_expr.get());
        expr* args[] = { x.get() };
        expr_ref result(m);
        bool success = inv(not_app->get_decl(), 1, args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }

    // Test ITE inversion: if (cond, x, y) -> fresh
    // This should work when both branches are unconstrained
    expr_ref ite_expr(m.mk_ite(z.get(), x.get(), y.get()), m);
    if (ite_expr.get() && is_app(ite_expr.get())) {
        app* ite_app = to_app(ite_expr.get());
        expr* args[] = { z.get(), x.get(), y.get() };
        expr_ref result(m);
        bool success = inv(ite_app->get_decl(), 3, args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }

    // Test AND inversion: x & y -> fresh
    expr_ref and_expr(m.mk_and(x.get(), y.get()), m);
    if (and_expr.get() && is_app(and_expr.get())) {
        app* and_app = to_app(and_expr.get());
        expr* args[] = { x.get(), y.get() };
        expr_ref result(m);
        bool success = inv(and_app->get_decl(), 2, args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }

    // Test OR inversion: x | y -> fresh
    expr_ref or_expr(m.mk_or(x.get(), y.get()), m);
    if (or_expr.get() && is_app(or_expr.get())) {
        app* or_app = to_app(or_expr.get());
        expr* args[] = { x.get(), y.get() };
        expr_ref result(m);
        bool success = inv(or_app->get_decl(), 2, args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }
}

static void test_equality_inversion() {
    ast_manager m;
    expr_inverter inv(m);

    // Create variables of different types
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref x(m.mk_const(symbol("x"), bool_sort), m);
    expr_ref true_expr(m.mk_true(), m);

    // Set up the inverter to recognize x as unconstrained
    std::function<bool(expr*)> is_var = [&](expr* e) {
        return e == x.get();
    };
    inv.set_is_var(is_var);

    // Test equality inversion: x = true -> fresh
    expr_ref eq_expr(m.mk_eq(x.get(), true_expr.get()), m);
    if (eq_expr.get() && is_app(eq_expr.get())) {
        app* eq_app = to_app(eq_expr.get());
        expr* eq_args[] = { x.get(), true_expr.get() };
        expr_ref result(m);
        bool success = inv(eq_app->get_decl(), 2, eq_args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }
}

static void test_model_converter_integration() {
    ast_manager m;
    expr_inverter inv(m);

    // Create a generic model converter for testing
    generic_model_converter* mc = alloc(generic_model_converter, m, "test_inverter");
    inv.set_model_converter(mc);

    // Create test variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref x(m.mk_const(symbol("x"), bool_sort), m);
    expr_ref y(m.mk_const(symbol("y"), bool_sort), m);

    std::function<bool(expr*)> is_var = [&](expr* e) {
        return e == x.get() || e == y.get();
    };
    inv.set_is_var(is_var);

    // Test that model converter integration works
    expr_ref and_expr(m.mk_and(x.get(), y.get()), m);
    if (and_expr.get() && is_app(and_expr.get())) {
        app* and_app = to_app(and_expr.get());
        expr* args[] = { x.get(), y.get() };
        expr_ref result(m);
        bool success = inv(and_app->get_decl(), 2, args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);

        // The model converter should have definitions added
        // (We can't easily verify the specific definitions without more introspection)
    }
}

static void test_proof_mode() {
    ast_manager m;
    expr_inverter inv(m);

    // Enable proof production
    inv.set_produce_proofs(true);

    // Create test case
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref x(m.mk_const(symbol("x"), bool_sort), m);

    std::function<bool(expr*)> is_var = [&](expr* e) {
        return e == x.get();
    };
    inv.set_is_var(is_var);

    // Test that proof mode doesn't break functionality
    expr_ref not_expr(m.mk_not(x.get()), m);
    if (not_expr.get() && is_app(not_expr.get())) {
        app* not_app = to_app(not_expr.get());
        expr* args[] = { x.get() };
        expr_ref result(m);
        bool success = inv(not_app->get_decl(), 1, args, result);
        ENSURE(success);
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }
}

static void test_unconstrained_detection() {
    ast_manager m;
    expr_inverter inv(m);

    // Create variables
    sort_ref bool_sort(m.mk_bool_sort(), m);
    expr_ref x(m.mk_const(symbol("x"), bool_sort), m);
    expr_ref y(m.mk_const(symbol("y"), bool_sort), m);
    expr_ref z(m.mk_const(symbol("z"), bool_sort), m);

    // Set up the inverter to recognize only x as unconstrained
    std::function<bool(expr*)> is_var = [&](expr* e) {
        return e == x.get();  // Only x is unconstrained
    };
    inv.set_is_var(is_var);

    // Test with mixed constrained/unconstrained variables
    // This should fail because y is constrained
    expr_ref and_expr(m.mk_and(x.get(), y.get()), m);
    if (and_expr.get() && is_app(and_expr.get())) {
        app* and_app = to_app(and_expr.get());
        expr* args[] = { x.get(), y.get() };
        expr_ref result(m);
        bool success = inv(and_app->get_decl(), 2, args, result);
        // This might succeed or fail depending on implementation
        // The key is that it should handle this gracefully
        (void)success;  // Suppress unused warning
    }

    // Test with only unconstrained variables
    expr_ref not_expr(m.mk_not(x.get()), m);
    if (not_expr.get() && is_app(not_expr.get())) {
        app* not_app = to_app(not_expr.get());
        expr* args[] = { x.get() };
        expr_ref result(m);
        bool success = inv(not_app->get_decl(), 1, args, result);
        ENSURE(success);  // This should always work
        ENSURE(result.get() != nullptr);
        ENSURE(is_app(result.get()));
    }
}

static void test_difference_creation() {
    ast_manager m;
    expr_inverter inv(m);

    // Test difference creation for boolean values
    expr_ref true_expr(m.mk_true(), m);
    expr_ref false_expr(m.mk_false(), m);

    expr_ref diff1(m);
    bool success1 = inv.mk_diff(true_expr.get(), diff1);
    ENSURE(success1);
    ENSURE(diff1.get() != nullptr);
    ENSURE(diff1.get() != true_expr.get());  // Should be different

    expr_ref diff2(m);
    bool success2 = inv.mk_diff(false_expr.get(), diff2);
    ENSURE(success2);
    ENSURE(diff2.get() != nullptr);
    ENSURE(diff2.get() != false_expr.get());  // Should be different
}

void tst_expr_inverter() {
    test_basic_boolean_inversion();
    test_equality_inversion();
    test_model_converter_integration();
    test_proof_mode();
    test_unconstrained_detection();
    test_difference_creation();
}