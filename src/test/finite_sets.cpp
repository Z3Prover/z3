/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    tst_finite_sets.cpp

Abstract:

    Test finite sets decl plugin

Author:

    GitHub Copilot Agent 2025

Revision History:

--*/
#include "ast/ast.h"
#include "ast/finite_sets_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"

static void tst_finite_sets_basic() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_sets_util fsets(m);
    arith_util arith(m);
    
    // Test creating a finite set sort
    sort_ref int_sort(arith.mk_int(), m);
    parameter param(int_sort.get());
    sort_ref finite_set_int(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &param), m);
    
    ENSURE(fsets.is_finite_set(finite_set_int.get()));
    
    // Test creating empty set
    app_ref empty_set(fsets.mk_empty(int_sort), m);
    ENSURE(fsets.is_empty(empty_set.get()));
    ENSURE(empty_set->get_sort() == finite_set_int.get());
    
    // Test set.singleton
    expr_ref five(arith.mk_int(5), m);
    app_ref singleton_set(fsets.mk_singleton(five), m);
    ENSURE(fsets.is_singleton(singleton_set.get()));
    ENSURE(singleton_set->get_sort() == finite_set_int.get());
    
    // Test set.range
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref range_set(fsets.mk_range(zero, ten), m);
    ENSURE(fsets.is_range(range_set.get()));
    ENSURE(range_set->get_sort() == finite_set_int.get());
    
    // Test set.union
    app_ref union_set(fsets.mk_union(empty_set, range_set), m);
    ENSURE(fsets.is_union(union_set.get()));
    ENSURE(union_set->get_sort() == finite_set_int.get());
    
    // Test set.intersect
    app_ref intersect_set(fsets.mk_intersect(range_set, range_set), m);
    ENSURE(fsets.is_intersect(intersect_set.get()));
    ENSURE(intersect_set->get_sort() == finite_set_int.get());
    
    // Test set.difference
    app_ref diff_set(fsets.mk_difference(range_set, empty_set), m);
    ENSURE(fsets.is_difference(diff_set.get()));
    ENSURE(diff_set->get_sort() == finite_set_int.get());
    
    // Test set.in
    app_ref in_expr(fsets.mk_in(five, range_set), m);
    ENSURE(fsets.is_in(in_expr.get()));
    ENSURE(m.is_bool(in_expr->get_sort()));
    
    // Test set.size
    app_ref size_expr(fsets.mk_size(range_set), m);
    ENSURE(fsets.is_size(size_expr.get()));
    ENSURE(arith.is_int(size_expr->get_sort()));
    
    // Test set.subset
    app_ref subset_expr(fsets.mk_subset(empty_set, range_set), m);
    ENSURE(fsets.is_subset(subset_expr.get()));
    ENSURE(m.is_bool(subset_expr->get_sort()));
}

static void tst_finite_sets_map_filter() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_sets_util fsets(m);
    arith_util arith(m);
    
    // Create Int and Bool sorts
    sort_ref int_sort(arith.mk_int(), m);
    sort_ref bool_sort(m.mk_bool_sort(), m);
    
    // Create finite set sorts
    parameter int_param(int_sort.get());
    sort_ref finite_set_int(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &int_param), m);
    
    // Create a function Int -> Int for map
    func_decl_ref inc_func(m.mk_func_decl(symbol("inc"), int_sort.get(), int_sort.get()), m);
    
    // Create a set and test map
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref range_set(fsets.mk_range(zero, ten), m);
    
    app_ref mapped_set(fsets.mk_map(inc_func, range_set), m);
    ENSURE(fsets.is_map(mapped_set.get()));
    ENSURE(mapped_set->get_sort() == finite_set_int.get());
    
    // Create a function Int -> Bool for filter
    func_decl_ref is_even(m.mk_func_decl(symbol("is_even"), int_sort.get(), bool_sort.get()), m);
    
    app_ref filtered_set(fsets.mk_filter(is_even, range_set), m);
    ENSURE(fsets.is_filter(filtered_set.get()));
    ENSURE(filtered_set->get_sort() == finite_set_int.get());
}

void tst_finite_sets() {
    tst_finite_sets_basic();
    tst_finite_sets_map_filter();
}
