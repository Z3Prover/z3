/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    array_peq.cpp

Abstract:

    Tests for array partial equality functionality

Author:

    Daily Test Coverage Improver

--*/
#include "ast/array_peq.h"
#include "ast/ast.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "util/debug.h"

// Test basic partial equality detection functions
void tst_array_peq() {
    ast_manager m;
    reg_decl_plugins(m);
    array_util arr_u(m);
    arith_util arith(m);

    // Create array sort: Array[Int, Int]
    sort* int_sort = arith.mk_int();
    sort* array_sort = arr_u.mk_array_sort(int_sort, int_sort);

    // Create two array expressions
    expr_ref a(m.mk_const(symbol("a"), array_sort), m);
    expr_ref b(m.mk_const(symbol("b"), array_sort), m);
    expr_ref i0(m.mk_const(symbol("i0"), int_sort), m);

    // Test mk_peq with single difference index
    vector<expr_ref_vector> diff_indices;
    expr_ref_vector single_index(m);
    single_index.push_back(i0);
    diff_indices.push_back(std::move(single_index));

    app_ref peq_expr = mk_peq(a, b, diff_indices, m);

    // Test partial equality detection functions
    ENSURE(is_partial_eq(peq_expr));
    ENSURE(is_peq(peq_expr));
    ENSURE(is_partial_eq(peq_expr->get_decl()));
    ENSURE(is_peq(peq_expr->get_decl()));

    // Test with non-partial equality
    expr_ref normal_eq(m.mk_eq(a, b), m);
    ENSURE(!is_partial_eq(normal_eq));
    ENSURE(!is_peq(normal_eq));

    // Test peq constructor from expressions
    peq partial_eq(a, b, diff_indices, m);

    // Test lhs/rhs accessors
    expr_ref lhs = partial_eq.lhs();
    expr_ref rhs = partial_eq.rhs();
    ENSURE(lhs == a);
    ENSURE(rhs == b);

    // Test mk_peq method
    app_ref peq_expr2 = partial_eq.mk_peq();
    ENSURE(is_partial_eq(peq_expr2));

    // Test caching - should return same object
    app_ref peq_expr3 = partial_eq.mk_peq();
    ENSURE(peq_expr2 == peq_expr3);

    // Test peq constructor from app
    peq from_app(peq_expr, m);
    expr_ref lhs2 = from_app.lhs();
    expr_ref rhs2 = from_app.rhs();
    ENSURE(lhs2 == a);
    ENSURE(rhs2 == b);

    // Test difference indices retrieval
    vector<expr_ref_vector> retrieved_indices;
    from_app.get_diff_indices(retrieved_indices);
    ENSURE(retrieved_indices.size() == 1);
    ENSURE(retrieved_indices[0].size() == 1);

    // Test mk_eq conversion with auxiliary constants
    app_ref_vector aux_consts(m);
    app_ref eq_expr = partial_eq.mk_eq(aux_consts, true);

    // Should have created auxiliary constants for the stores
    ENSURE(aux_consts.size() == 1);
    ENSURE(m.is_eq(eq_expr));

    // Test caching for mk_eq
    app_ref_vector aux_consts2(m);
    app_ref eq_expr2 = partial_eq.mk_eq(aux_consts2, true);
    ENSURE(eq_expr == eq_expr2); // Should return cached object
    ENSURE(aux_consts2.size() == 0); // No new constants on cached call
}

// Test with multiple indices
void tst_array_peq_multi() {
    ast_manager m;
    reg_decl_plugins(m);
    array_util arr_u(m);
    arith_util arith(m);

    sort* int_sort = arith.mk_int();
    sort* array_sort = arr_u.mk_array_sort(int_sort, int_sort);

    expr_ref a(m.mk_const(symbol("a"), array_sort), m);
    expr_ref b(m.mk_const(symbol("b"), array_sort), m);
    expr_ref i0(m.mk_const(symbol("i0"), int_sort), m);
    expr_ref i1(m.mk_const(symbol("i1"), int_sort), m);

    // Test mk_peq with multiple difference indices
    vector<expr_ref_vector> diff_indices;

    expr_ref_vector index1(m);
    index1.push_back(i0);
    diff_indices.push_back(std::move(index1));

    expr_ref_vector index2(m);
    index2.push_back(i1);
    diff_indices.push_back(std::move(index2));

    peq partial_eq(a, b, diff_indices, m);

    // Verify partial equality
    app_ref peq_expr = partial_eq.mk_peq();
    ENSURE(is_partial_eq(peq_expr));

    // Test mk_eq with multiple indices
    app_ref_vector aux_consts(m);
    app_ref eq_expr = partial_eq.mk_eq(aux_consts, true);

    // Should have created two auxiliary constants (one per index)
    ENSURE(aux_consts.size() == 2);
    ENSURE(m.is_eq(eq_expr));
}

// Test edge cases
void tst_array_peq_edge() {
    ast_manager m;
    reg_decl_plugins(m);
    array_util arr_u(m);
    arith_util arith(m);

    sort* int_sort = arith.mk_int();
    sort* array_sort = arr_u.mk_array_sort(int_sort, int_sort);

    expr_ref a(m.mk_const(symbol("a"), array_sort), m);
    expr_ref b(m.mk_const(symbol("b"), array_sort), m);

    // Test with empty difference indices
    vector<expr_ref_vector> empty_diff_indices;
    peq partial_eq(a, b, empty_diff_indices, m);

    // Should still work with no difference indices
    app_ref peq_expr = partial_eq.mk_peq();
    ENSURE(is_partial_eq(peq_expr));

    // mk_eq with empty indices should work
    app_ref_vector aux_consts(m);
    app_ref eq_expr = partial_eq.mk_eq(aux_consts, true);
    ENSURE(aux_consts.size() == 0); // No indices, no auxiliary constants
    ENSURE(m.is_eq(eq_expr));

    // Test stores_on_rhs = false
    app_ref_vector aux_consts2(m);
    app_ref eq_expr2 = partial_eq.mk_eq(aux_consts2, false);
    ENSURE(aux_consts2.size() == 0);
    ENSURE(m.is_eq(eq_expr2));
}