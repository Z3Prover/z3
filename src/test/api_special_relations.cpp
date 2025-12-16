/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_special_relations.cpp

Abstract:

    Test API special relations functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"

void tst_api_special_relations() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Create a sort for testing
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort univ_sort = Z3_mk_uninterpreted_sort(ctx, Z3_mk_string_symbol(ctx, "U"));

    // Test Z3_mk_linear_order
    {
        Z3_func_decl linear_order = Z3_mk_linear_order(ctx, int_sort, 0);
        ENSURE(linear_order != nullptr);
        ENSURE(Z3_get_decl_name(ctx, linear_order) != nullptr);

        // Test with uninterpreted sort
        Z3_func_decl linear_order2 = Z3_mk_linear_order(ctx, univ_sort, 1);
        ENSURE(linear_order2 != nullptr);
        ENSURE(linear_order2 != linear_order); // Different indexes should create different functions
    }

    // Test Z3_mk_partial_order
    {
        Z3_func_decl partial_order = Z3_mk_partial_order(ctx, int_sort, 0);
        ENSURE(partial_order != nullptr);
        ENSURE(Z3_get_decl_name(ctx, partial_order) != nullptr);

        // Test with different index
        Z3_func_decl partial_order2 = Z3_mk_partial_order(ctx, int_sort, 2);
        ENSURE(partial_order2 != nullptr);
        ENSURE(partial_order2 != partial_order);
    }

    // Test Z3_mk_piecewise_linear_order
    {
        Z3_func_decl piecewise_linear_order = Z3_mk_piecewise_linear_order(ctx, int_sort, 0);
        ENSURE(piecewise_linear_order != nullptr);
        ENSURE(Z3_get_decl_name(ctx, piecewise_linear_order) != nullptr);

        // Test with uninterpreted sort
        Z3_func_decl piecewise_linear_order2 = Z3_mk_piecewise_linear_order(ctx, univ_sort, 3);
        ENSURE(piecewise_linear_order2 != nullptr);
        ENSURE(piecewise_linear_order2 != piecewise_linear_order);
    }

    // Test Z3_mk_tree_order
    {
        Z3_func_decl tree_order = Z3_mk_tree_order(ctx, int_sort, 0);
        ENSURE(tree_order != nullptr);
        ENSURE(Z3_get_decl_name(ctx, tree_order) != nullptr);

        // Test with different index
        Z3_func_decl tree_order2 = Z3_mk_tree_order(ctx, int_sort, 4);
        ENSURE(tree_order2 != nullptr);
        ENSURE(tree_order2 != tree_order);
    }

    // Test Z3_mk_transitive_closure
    {
        // First create a binary relation
        Z3_sort domain[2] = { int_sort, int_sort };
        Z3_func_decl relation = Z3_mk_func_decl(ctx,
            Z3_mk_string_symbol(ctx, "R"),
            2, domain,
            Z3_mk_bool_sort(ctx));

        Z3_func_decl transitive_closure = Z3_mk_transitive_closure(ctx, relation);
        ENSURE(transitive_closure != nullptr);
        ENSURE(Z3_get_decl_name(ctx, transitive_closure) != nullptr);

        // Test with another relation
        Z3_func_decl relation2 = Z3_mk_func_decl(ctx,
            Z3_mk_string_symbol(ctx, "S"),
            2, domain,
            Z3_mk_bool_sort(ctx));

        Z3_func_decl transitive_closure2 = Z3_mk_transitive_closure(ctx, relation2);
        ENSURE(transitive_closure2 != nullptr);
        ENSURE(transitive_closure2 != transitive_closure);
    }

    // Test integration: create expressions using the special relations
    {
        Z3_func_decl linear_order = Z3_mk_linear_order(ctx, int_sort, 0);

        // Create some integer constants
        Z3_ast x = Z3_mk_int(ctx, 1, int_sort);
        Z3_ast y = Z3_mk_int(ctx, 2, int_sort);

        Z3_ast args[2] = { x, y };
        Z3_ast expr = Z3_mk_app(ctx, linear_order, 2, args);
        ENSURE(expr != nullptr);
        ENSURE(Z3_get_sort(ctx, expr) == Z3_mk_bool_sort(ctx));
    }

    Z3_del_context(ctx);
}