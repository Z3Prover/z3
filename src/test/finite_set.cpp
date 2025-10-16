/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    tst_finite_set.cpp

Abstract:

    Test finite sets decl plugin

Author:

    GitHub Copilot Agent 2025

Revision History:

--*/
#include "ast/ast.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"

static void tst_finite_set_basic() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    arith_util arith(m);
    
    // Test creating a finite set sort
    sort_ref int_sort(arith.mk_int(), m);
    parameter param(int_sort.get());
    sort_ref finite_set_int(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &param), m);
    
    ENSURE(fsets.is_finite_set(finite_set_int.get()));
    
    // Test creating empty set
    app_ref empty_set(fsets.mk_empty(finite_set_int), m);
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

static void tst_finite_set_map_select() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    arith_util arith(m);
    array_util autil(m);
    
    // Create Int and Bool sorts
    sort_ref int_sort(arith.mk_int(), m);
    sort_ref bool_sort(m.mk_bool_sort(), m);
    
    // Create finite set sorts
    parameter int_param(int_sort.get());
    sort_ref finite_set_int(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &int_param), m);
    
    // Create Array (Int Int) sort for map
    sort_ref arr_int_int(autil.mk_array_sort(int_sort, int_sort), m);
    
    // Create a const array (conceptually represents the function)
    app_ref arr_map(autil.mk_const_array(arr_int_int, arith.mk_int(42)), m);
    
    // Create a set and test map
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref range_set(fsets.mk_range(zero, ten), m);
    
    app_ref mapped_set(fsets.mk_map(arr_map, range_set), m);
    ENSURE(fsets.is_map(mapped_set.get()));
    ENSURE(fsets.is_finite_set(mapped_set->get_sort()));
    
    // Create Array (Int Bool) sort for select
    sort_ref arr_int_bool(autil.mk_array_sort(int_sort, bool_sort), m);
    
    // Create a const array for select (conceptually represents predicate)
    app_ref arr_select(autil.mk_const_array(arr_int_bool, m.mk_true()), m);
    
    app_ref selected_set(fsets.mk_select(arr_select, range_set), m);
    ENSURE(fsets.is_select(selected_set.get()));
    ENSURE(selected_set->get_sort() == finite_set_int.get());
}

static void tst_finite_set_is_value() {
    ast_manager m;
    reg_decl_plugins(m);
    

    
    finite_set_util fsets(m);
    arith_util arith(m);
    finite_set_decl_plugin* plugin = static_cast<finite_set_decl_plugin*>(m.get_plugin(fsets.get_family_id()));
  
      // Create Int sort and finite set sort
    
    // Test with Int sort (should be fully interpreted)
    sort_ref int_sort(arith.mk_int(), m);
    parameter int_param(int_sort.get());
    sort_ref finite_set_int(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &int_param), m);
    
    
  // Test 1: Empty set is a value
    app_ref empty_set(fsets.mk_empty(finite_set_int), m);
    ENSURE(plugin->is_value(empty_set.get()));
    
    // Test 2: Singleton with value element is a value
    expr_ref five(arith.mk_int(5), m);
    app_ref singleton_five(fsets.mk_singleton(five), m);
    ENSURE(plugin->is_value(singleton_five.get()));
    
    // Test 3: Union of empty and singleton is a value
    app_ref union_empty_singleton(fsets.mk_union(empty_set, singleton_five), m);
    ENSURE(plugin->is_value(union_empty_singleton.get()));
    
    // Test 4: Union of two singletons with value elements is a value
    expr_ref seven(arith.mk_int(7), m);
    app_ref singleton_seven(fsets.mk_singleton(seven), m);
    app_ref union_two_singletons(fsets.mk_union(singleton_five, singleton_seven), m);
    ENSURE(plugin->is_value(union_two_singletons.get()));
    
    // Test 5: Nested union of singletons and empty sets is a value
    app_ref union_nested(fsets.mk_union(union_empty_singleton, singleton_seven), m);
    ENSURE(plugin->is_value(union_nested.get()));
    
    // Test 6: Union with empty set is a value
    app_ref union_empty_empty(fsets.mk_union(empty_set, empty_set), m);
    ENSURE(plugin->is_value(union_empty_empty.get()));
    
    // Test 7: Triple union is a value
    expr_ref nine(arith.mk_int(9), m);
    app_ref singleton_nine(fsets.mk_singleton(nine), m);
    app_ref union_temp(fsets.mk_union(singleton_five, singleton_seven), m);
    app_ref union_triple(fsets.mk_union(union_temp, singleton_nine), m);
    ENSURE(plugin->is_value(union_triple.get()));
    
    // Test 8: Range is NOT a value (it's not a union of empty/singletons)
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref range_set(fsets.mk_range(zero, ten), m);
    ENSURE(!plugin->is_value(range_set.get()));
    
    // Test 9: Union with range is NOT a value
    app_ref union_with_range(fsets.mk_union(singleton_five, range_set), m);
    ENSURE(!plugin->is_value(union_with_range.get()));
    
    // Test 10: Intersect is NOT a value
    app_ref intersect_set(fsets.mk_intersect(singleton_five, singleton_seven), m);
    ENSURE(!plugin->is_value(intersect_set.get()));
    ENSURE(m.is_fully_interp(int_sort));
    ENSURE(m.is_fully_interp(finite_set_int));
}

static void tst_finite_set_is_fully_interp() {
    ast_manager m;
    reg_decl_plugins(m);
    
    // Test with Bool sort (should be fully interpreted)
    sort_ref bool_sort(m.mk_bool_sort(), m);
    parameter bool_param(bool_sort.get());
    sort_ref finite_set_bool(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &bool_param), m);
    
    ENSURE(m.is_fully_interp(bool_sort));
    ENSURE(m.is_fully_interp(finite_set_bool));
    
    // Test with uninterpreted sort (should not be fully interpreted)
    sort_ref uninterp_sort(m.mk_uninterpreted_sort(symbol("U")), m);
    parameter uninterp_param(uninterp_sort.get());
    sort_ref finite_set_uninterp(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &uninterp_param), m);
    
    ENSURE(!m.is_fully_interp(uninterp_sort));
    ENSURE(!m.is_fully_interp(finite_set_uninterp));
}

void tst_finite_set() {
    tst_finite_set_basic();
    tst_finite_set_map_select();
    tst_finite_set_is_value();
    tst_finite_set_is_fully_interp();
}
