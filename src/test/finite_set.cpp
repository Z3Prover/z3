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
#include "api/z3.h"
#include "ast/ast.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/simplifiers/finite_set_simplifier.h"
#include <string>

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

static void tst_finite_set_map_filter() {
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
    
    // Create Array (Int Bool) sort for filter
    sort_ref arr_int_bool(autil.mk_array_sort(int_sort, bool_sort), m);
    
    // Create a const array for filter (conceptually represents predicate)
    app_ref arr_filter(autil.mk_const_array(arr_int_bool, m.mk_true()), m);
    
    app_ref filtered_set(fsets.mk_filter(arr_filter, range_set), m);
    ENSURE(fsets.is_filter(filtered_set.get()));
    ENSURE(filtered_set->get_sort() == finite_set_int.get());
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
    
    // Test 8: Range is a value
    expr_ref zero(arith.mk_int(0), m);
    expr_ref ten(arith.mk_int(10), m);
    app_ref range_set(fsets.mk_range(zero, ten), m);
    ENSURE(plugin->is_value(range_set.get()));
    
    // Test 9: Union with range is  a value
    app_ref union_with_range(fsets.mk_union(singleton_five, range_set), m);
    ENSURE(plugin->is_value(union_with_range.get()));
    
    // Test 10: Intersect is a value
    app_ref intersect_set(fsets.mk_intersect(singleton_five, singleton_seven), m);
    ENSURE(plugin->is_value(intersect_set.get()));
    ENSURE(m.is_fully_interp(int_sort));
    ENSURE(m.is_fully_interp(finite_set_int));
}

static void tst_finite_set_is_fully_interp() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    
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

static void tst_finite_set_sort_size() {
    ast_manager m;
    reg_decl_plugins(m);
    
    finite_set_util fsets(m);
    
    // Test 1: Bool sort (size 2) -> FiniteSet(Bool) should have size 2^2 = 4
    sort_ref bool_sort(m.mk_bool_sort(), m);
    parameter bool_param(bool_sort.get());
    sort_ref finite_set_bool(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &bool_param), m);
    
    sort_size const& bool_set_sz = finite_set_bool->get_num_elements();
    ENSURE(bool_set_sz.is_finite());
    ENSURE(!bool_set_sz.is_very_big());
    ENSURE(bool_set_sz.size() == 4); // 2^2 = 4
    
    // Test 2: Create a finite sort with known size (e.g., BV with size 3)
    // BV[3] has 2^3 = 8 elements, so FiniteSet(BV[3]) should have 2^8 = 256 elements
    parameter bv_param(3);
    sort_ref bv3_sort(m.mk_sort(m.mk_family_id("bv"), 0, 1, &bv_param), m);
    parameter bv3_param(bv3_sort.get());
    sort_ref finite_set_bv3(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &bv3_param), m);
    
    sort_size const& bv3_set_sz = finite_set_bv3->get_num_elements();
    ENSURE(bv3_set_sz.is_finite());
    ENSURE(!bv3_set_sz.is_very_big());
    ENSURE(bv3_set_sz.size() == 256); // 2^8 = 256
    
    // Test 3: BV with size 5 -> BV[5] has 2^5 = 32 elements
    // Since 32 > 30, FiniteSet(BV[5]) should be marked as very_big
    parameter bv5_param(5);
    sort_ref bv5_sort(m.mk_sort(m.mk_family_id("bv"), 0, 1, &bv5_param), m);
    parameter bv5_set_param(bv5_sort.get());
    sort_ref finite_set_bv5(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &bv5_set_param), m);
    
    sort_size const& bv5_set_sz = finite_set_bv5->get_num_elements();
    ENSURE(bv5_set_sz.is_very_big());
    
    // Test 4: Int sort (infinite) -> FiniteSet(Int) should be infinite
    arith_util arith(m);
    sort_ref int_sort(arith.mk_int(), m);
    parameter int_param(int_sort.get());
    sort_ref finite_set_int(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &int_param), m);
    
    sort_size const& int_set_sz = finite_set_int->get_num_elements();
    ENSURE(int_set_sz.is_infinite());
    
    // Test 5: BV with size 4 -> BV[4] has 2^4 = 16 elements
    // FiniteSet(BV[4]) should have 2^16 = 65536 elements
    parameter bv4_param(4);
    sort_ref bv4_sort(m.mk_sort(m.mk_family_id("bv"), 0, 1, &bv4_param), m);
    parameter bv4_set_param(bv4_sort.get());
    sort_ref finite_set_bv4(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &bv4_set_param), m);
    
    sort_size const& bv4_set_sz = finite_set_bv4->get_num_elements();
    ENSURE(bv4_set_sz.is_finite());
    ENSURE(!bv4_set_sz.is_very_big());
    ENSURE(bv4_set_sz.size() == 65536); // 2^16 = 65536
}

static void tst_finite_set_size_members() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort set_sort = Z3_mk_finite_set_sort(ctx, int_sort);
    Z3_ast s = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "s"), set_sort);
    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), int_sort);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), int_sort);
    Z3_solver_assert(ctx, solver, Z3_mk_finite_set_member(ctx, a, s));
    Z3_solver_assert(ctx, solver, Z3_mk_finite_set_member(ctx, b, s));
    Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, Z3_mk_finite_set_size(ctx, s), Z3_mk_int(ctx, 1, int_sort)));
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_ast elems[] = { a, b };
    Z3_solver_push(ctx, solver);
    Z3_solver_assert(ctx, solver, Z3_mk_distinct(ctx, 2, elems));
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
    Z3_solver_pop(ctx, solver, 1);
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);
    Z3_del_config(cfg);
}

static void tst_finite_set_size_three_members() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort set_sort = Z3_mk_finite_set_sort(ctx, int_sort);
    Z3_ast s = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "s"), set_sort);
    Z3_ast x = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "x"), int_sort);
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), int_sort);
    Z3_ast z = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "z"), int_sort);
    Z3_solver_assert(ctx, solver, Z3_mk_finite_set_member(ctx, x, s));
    Z3_solver_assert(ctx, solver, Z3_mk_finite_set_member(ctx, y, s));
    Z3_solver_assert(ctx, solver, Z3_mk_finite_set_member(ctx, z, s));
    Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, Z3_mk_finite_set_size(ctx, s), Z3_mk_int(ctx, 2, int_sort)));
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_ast elems[] = { x, y, z };
    Z3_solver_push(ctx, solver);
    Z3_solver_assert(ctx, solver, Z3_mk_distinct(ctx, 3, elems));
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
    Z3_solver_pop(ctx, solver, 1);
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);
    Z3_del_config(cfg);
}

static void tst_finite_set_size_union_singletons() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
    Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
    Z3_ast singleton_one = Z3_mk_finite_set_singleton(ctx, one);
    Z3_ast singleton_two = Z3_mk_finite_set_singleton(ctx, two);
    Z3_ast set = Z3_mk_finite_set_union(ctx, singleton_one, singleton_two);
    Z3_ast size = Z3_mk_finite_set_size(ctx, set);
    Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, size, Z3_mk_int(ctx, 2, int_sort)));

    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);
    Z3_del_config(cfg);
}

static void tst_finite_set_quantified_membership() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    char const* spec =
        "(set-logic ALL)\n"
        "(declare-const S (FiniteSet Int))\n"
        "(assert (not (set.in 0 S)))\n"
        "(assert (forall ((x Int)) (=> (= (mod x 2) 0) (set.in (mod x 2) S))))\n"
        "(check-sat)\n";
    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    ENSURE(response == "unsat\n");
    Z3_del_context(ctx);
}

static void tst_finite_set_lambda_filter() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_solver_push(ctx, solver);
    Z3_solver_from_string(ctx, solver,
        "(declare-const a (Array Bool Bool))"
        "(assert (distinct a (lambda ((x Bool))"
        " (set.in x (set.filter a"
        " (set.union (set.singleton false) (set.singleton true)))))))");
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
    Z3_solver_pop(ctx, solver, 1);
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_solver_from_string(ctx, solver,
        "(declare-const b (Array Bool Bool))"
        "(assert (distinct"
        " (lambda ((x Bool)) (and (not x) (select b x)))"
        " (lambda ((x Bool))"
        " (set.in x (set.filter b (set.singleton false))))))");
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);
    Z3_del_config(cfg);
}

static bool eval_finite_set_bool(Z3_context ctx, Z3_ast value) {
    value = Z3_simplify(ctx, value);
    auto b = Z3_get_bool_value(ctx, value);
    if (b != Z3_L_UNDEF)
        return b == Z3_L_TRUE;
    Z3_app app = Z3_to_app(ctx, value);
    auto kind = Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, app));
    if (kind == Z3_OP_NOT)
        return !eval_finite_set_bool(ctx, Z3_get_app_arg(ctx, app, 0));
    ENSURE(kind == Z3_OP_FINITE_SET_IN);
    Z3_ast elem = Z3_get_app_arg(ctx, app, 0);
    svector<Z3_ast> todo;
    todo.push_back(Z3_get_app_arg(ctx, app, 1));
    while (!todo.empty()) {
        Z3_app set = Z3_to_app(ctx, todo.back());
        todo.pop_back();
        switch (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, set))) {
        case Z3_OP_FINITE_SET_EMPTY:
            break;
        case Z3_OP_FINITE_SET_SINGLETON: {
            Z3_ast eq = Z3_mk_eq(ctx, elem, Z3_get_app_arg(ctx, set, 0));
            auto equal = Z3_get_bool_value(ctx, Z3_simplify(ctx, eq));
            ENSURE(equal != Z3_L_UNDEF);
            if (equal == Z3_L_TRUE)
                return true;
            break;
        }
        case Z3_OP_FINITE_SET_UNION:
            todo.push_back(Z3_get_app_arg(ctx, set, 0));
            todo.push_back(Z3_get_app_arg(ctx, set, 1));
            break;
        default:
            ENSURE(false);
        }
    }
    return false;
}

static void check_finite_set_model(Z3_context ctx, Z3_solver solver) {
    Z3_model model = Z3_solver_get_model(ctx, solver);
    Z3_model_inc_ref(ctx, model);
    Z3_ast_vector assertions = Z3_solver_get_assertions(ctx, solver);
    Z3_ast_vector_inc_ref(ctx, assertions);
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions); ++i) {
        Z3_ast value = nullptr;
        ENSURE(Z3_model_eval(ctx, model, Z3_ast_vector_get(ctx, assertions, i), true, &value));
        value = Z3_simplify(ctx, value);
        bool valid = eval_finite_set_bool(ctx, value);
        if (!valid)
            std::cout << "model:\n" << Z3_model_to_string(ctx, model)
                      << "\nassertion: " << Z3_ast_to_string(ctx, Z3_ast_vector_get(ctx, assertions, i))
                      << "\nvalue: " << Z3_ast_to_string(ctx, value) << "\n";
        ENSURE(valid);
    }
    Z3_ast_vector_dec_ref(ctx, assertions);
    Z3_model_dec_ref(ctx, model);
}

static void tst_finite_set_lambda_predicates(bool reuse_witness) {
    struct test_case {
        char const* formula;
        Z3_lbool expected;
        bool existing_witness = false;
    };
    test_case cases[] = {
        {
            "(declare-datatype T ((mk-t (value Int) (flag Bool))))"
            "(declare-const s (FiniteSet T))"
            "(assert (distinct"
            " (set.filter (lambda ((x T)) (flag x)) s)"
            " (as set.empty (FiniteSet T))))",
            Z3_L_TRUE
        },
        {
            "(declare-datatype T ((mk-t (value Int))))"
            "(declare-const s (FiniteSet T))"
            "(declare-const t (FiniteSet T))"
            "(assert (distinct s (as set.empty (FiniteSet T))))"
            "(assert (= s (set.filter (lambda ((x T))"
            " (distinct (set.filter (lambda ((y T)) (= (value x) (value y))) t)"
            " (as set.empty (FiniteSet T)))) s)))",
            Z3_L_TRUE
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(assert (set.in 0 s))"
            "(assert (= (set.filter (lambda ((x Int)) (>= x 0)) s)"
            " (as set.empty (FiniteSet Int))))",
            Z3_L_FALSE
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(declare-const p (Array Int Bool))"
            "(assert (set.in 0 s))"
            "(assert (= (set.filter p s) (as set.empty (FiniteSet Int))))"
            "(assert (select p 0))",
            Z3_L_FALSE
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(declare-const t (FiniteSet (FiniteSet Int)))"
            "(assert (set.in 0 s))"
            "(assert (= t (set.singleton s)))",
            Z3_L_TRUE
        },
        {
            "(declare-datatype T ((mk-t (key Int) (flag Bool))))"
            "(declare-const s (FiniteSet T))"
            "(assert (distinct s (as set.empty (FiniteSet T))))"
            "(assert (= s (set.filter (lambda ((x T))"
            " (= s (set.filter (lambda ((y T))"
            " (=> (= (key x) (key y)) (= x y))) s))) s)))",
            Z3_L_TRUE
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(declare-const t (FiniteSet Int))"
            "(declare-const x Int)"
            "(declare-const y Int)"
            "(assert (= x y))"
            "(assert (set.in x s))"
            "(assert (not (set.in y t)))"
            "(assert (distinct s t))",
            Z3_L_TRUE, true
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(assert (set.in 0 s))"
            "(assert (distinct s (as set.empty (FiniteSet Int))))",
            Z3_L_TRUE, true
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(assert (set.in 0 s))"
            "(assert (distinct (as set.empty (FiniteSet Int)) s))",
            Z3_L_TRUE, true
        },
        {
            "(declare-const s (FiniteSet Int))"
            "(declare-const t (FiniteSet Int))"
            "(assert (set.in 0 s))"
            "(assert (set.in 0 t))"
            "(assert (= (set.size s) 1))"
            "(assert (= (set.size t) 1))"
            "(assert (distinct s t))",
            Z3_L_FALSE
        }
    };
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_params params = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, params);
    Z3_params_set_bool(ctx, params, Z3_mk_string_symbol(ctx, "finite_set.reuse_witness"), reuse_witness);
    for (auto const& test : cases) {
        Z3_solver_reset(ctx, solver);
        Z3_solver_set_params(ctx, solver, params);
        Z3_solver_from_string(ctx, solver, test.formula);
        ENSURE(Z3_solver_check(ctx, solver) == test.expected);
        if (test.existing_witness && reuse_witness) {
            Z3_stats stats = Z3_solver_get_statistics(ctx, solver);
            Z3_stats_inc_ref(ctx, stats);
            bool skipped = false;
            for (unsigned i = 0; i < Z3_stats_size(ctx, stats); ++i)
                if (std::string(Z3_stats_get_key(ctx, stats, i)) == "finite-set-extensionality-skipped")
                    skipped = Z3_stats_get_uint_value(ctx, stats, i) > 0;
            ENSURE(skipped);
            Z3_stats_dec_ref(ctx, stats);
        }
        if (test.expected != Z3_L_TRUE)
            continue;
        check_finite_set_model(ctx, solver);
    }
    Z3_solver_reset(ctx, solver);
    Z3_solver_set_params(ctx, solver, params);
    Z3_solver_from_string(ctx, solver,
        "(declare-const s (FiniteSet Int))"
        "(declare-const t (FiniteSet Int))");
    char const* scopes[] = {
        "(assert (set.in 0 s))"
        "(assert (not (set.in 0 t)))"
        "(assert (distinct s t))",
        "(assert (not (set.in 0 s)))"
        "(assert (not (set.in 0 t)))"
        "(assert (distinct s t))"
    };
    for (auto scope : scopes) {
        Z3_solver_push(ctx, solver);
        Z3_solver_from_string(ctx, solver, scope);
        ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
        check_finite_set_model(ctx, solver);
        Z3_solver_pop(ctx, solver, 1);
    }
    Z3_solver_reset(ctx, solver);
    Z3_solver_set_params(ctx, solver, params);
    Z3_solver_from_string(ctx, solver,
        "(declare-const s (FiniteSet Int))"
        "(assert (distinct (set.filter (lambda ((x Int)) (>= x 0)) s)"
        " (as set.empty (FiniteSet Int))))");
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_ast_vector assertions = Z3_solver_get_assertions(ctx, solver);
    Z3_ast_vector_inc_ref(ctx, assertions);
    Z3_app assertion = Z3_to_app(ctx, Z3_ast_vector_get(ctx, assertions, 0));
    Z3_app filter = Z3_to_app(ctx, Z3_get_app_arg(ctx, assertion, 0));
    Z3_ast predicate = Z3_get_app_arg(ctx, filter, 0);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol name = Z3_mk_string_symbol(ctx, "x");
    Z3_ast variable = Z3_mk_bound(ctx, 0, int_sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast negative = Z3_mk_lt(ctx, variable, zero);
    Z3_ast complement = Z3_mk_lambda(ctx, 1, &int_sort, &name, negative);
    Z3_ast lhs = Z3_mk_array_default(ctx, predicate);
    Z3_ast rhs = Z3_mk_array_default(ctx, complement);
    Z3_solver_push(ctx, solver);
    Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, lhs, rhs));
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
    Z3_solver_pop(ctx, solver, 1);
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_ast_vector_dec_ref(ctx, assertions);
    Z3_params_dec_ref(ctx, params);
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);
}

static void check_finite_set_simplification(char const* input, char const* expected) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    std::string source = R"(
        (declare-const S (FiniteSet Int))
        (declare-const T (FiniteSet Int))
        (declare-const R (FiniteSet Real))
        (declare-const c Int)
        (declare-const r Real)
        (declare-const b Bool)
        (declare-fun p (Int) Bool)
        (declare-fun f (Int) Int)
        (declare-fun h (Int Int) Int)
        (declare-datatype Clock ((tick (time Int))))
        (declare-const C (FiniteSet Clock))
        (declare-datatype Pair ((pair (first Int) (second Int))))
        (declare-const P (FiniteSet Pair))
        (declare-datatype Maybe ((none) (some (value Int))))
        (declare-const M (FiniteSet Maybe))
    )";
    source += "(assert " + std::string(input) + ")(assert " + expected + ")";
    Z3_ast_vector assertions = Z3_parse_smtlib2_string(ctx, source.c_str(), 0, nullptr, nullptr, 0, nullptr, nullptr);
    Z3_ast_vector_inc_ref(ctx, assertions);
    ENSURE(Z3_ast_vector_size(ctx, assertions) == 2);
    Z3_goal goal = Z3_mk_goal(ctx, true, false, false);
    Z3_goal_inc_ref(ctx, goal);
    Z3_goal_assert(ctx, goal, Z3_ast_vector_get(ctx, assertions, 0));
    Z3_tactic tactic = Z3_mk_tactic(ctx, "finite-set-simplify");
    Z3_tactic_inc_ref(ctx, tactic);
    Z3_apply_result result = Z3_tactic_apply(ctx, tactic, goal);
    Z3_apply_result_inc_ref(ctx, result);
    ENSURE(Z3_apply_result_get_num_subgoals(ctx, result) == 1);
    Z3_goal simplified = Z3_apply_result_get_subgoal(ctx, result, 0);
    svector<Z3_ast> formulas;
    for (unsigned i = 0; i < Z3_goal_size(ctx, simplified); ++i)
        formulas.push_back(Z3_goal_formula(ctx, simplified, i));
    Z3_ast actual = Z3_simplify(ctx, Z3_mk_and(ctx, formulas.size(), formulas.data()));
    Z3_ast wanted = Z3_simplify(ctx, Z3_ast_vector_get(ctx, assertions, 1));
    if (!Z3_is_eq_ast(ctx, actual, wanted)) {
        std::cout << "Input: " << input << "\nActual: " << Z3_ast_to_string(ctx, actual)
                  << "\nExpected: " << Z3_ast_to_string(ctx, wanted) << "\n";
        ENSURE(false);
    }
    Z3_apply_result_dec_ref(ctx, result);
    Z3_tactic_dec_ref(ctx, tactic);
    Z3_goal_dec_ref(ctx, goal);
    Z3_ast_vector_dec_ref(ctx, assertions);
    Z3_del_context(ctx);
}

static void tst_finite_set_simplifier() {
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) b) S) S)",
        "(or (= S (as set.empty (FiniteSet Int))) b)");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) b) S) (as set.empty (FiniteSet Int)))",
        "(or (= S (as set.empty (FiniteSet Int))) (not b))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) (p x)) (as set.empty (FiniteSet Int))) (as set.empty (FiniteSet Int)))",
        "true");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) (and (= c x) (p x))) S) (as set.empty (FiniteSet Int)))",
        "(not (and (set.in c S) (p c)))");
    check_finite_set_simplification(
        "(= S (set.filter (lambda ((x Int)) (and (= x c) (p x))) S))",
        "(or (= S (as set.empty (FiniteSet Int))) (and (= S (set.singleton c)) (p c)))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Clock)) (and (<= c (time x)) (<= (time x) (+ c 0)))) C) (as set.empty (FiniteSet Clock)))",
        "(not (set.in (tick c) C))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Clock)) (and (= (time x) c) (p (time x)))) C) C)",
        "(or (= C (as set.empty (FiniteSet Clock))) (and (= C (set.singleton (tick c))) (p c)))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) (=> b (p x))) S) S)",
        "(or (not b) (= (set.filter (lambda ((x Int)) (p x)) S) S))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) (or b (p x))) S) S)",
        "(or b (= (set.filter (lambda ((x Int)) (p x)) S) S))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((x Int)) (and b (p x))) S) (as set.empty (FiniteSet Int)))",
        "(or (not b) (= (set.filter (lambda ((x Int)) (p x)) S) (as set.empty (FiniteSet Int))))");
    check_finite_set_simplification(
        "(forall ((c Int)) (= (set.filter (lambda ((x Int)) (> c 0)) S) S))",
        "(forall ((c Int)) (or (= S (as set.empty (FiniteSet Int))) (> c 0)))");
    check_finite_set_simplification(
        "(forall ((c Int)) (= (set.filter (lambda ((x Int)) (and (= x c) (forall ((y Int)) (p (+ x y))))) S) (as set.empty (FiniteSet Int))))",
        "(forall ((c Int)) (not (and (set.in c S) (forall ((y Int)) (p (+ c y))))))");
    check_finite_set_simplification(
        "(forall ((c Int)) (= (set.filter (lambda ((x Int)) (and (= x c) (= (set.filter (lambda ((y Int)) (= y x)) T) (as set.empty (FiniteSet Int))))) S) (as set.empty (FiniteSet Int))))",
        "(forall ((c Int)) (not (and (set.in c S) (not (set.in c T)))))");
    check_finite_set_simplification(
        "(not (= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= x hi)) S) S)) S) (as set.empty (FiniteSet Int))))",
        "(not (= S (as set.empty (FiniteSet Int))))");
    check_finite_set_simplification(
        "(= (as set.empty (FiniteSet Int)) (set.filter (lambda ((lo Int)) (= S (set.filter (lambda ((x Int)) (>= (f x) (f lo))) S))) S))",
        "(= S (as set.empty (FiniteSet Int)))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((hi Clock)) (= (set.filter (lambda ((x Clock)) (<= (time hi) (time x))) C) C)) C) (as set.empty (FiniteSet Clock)))",
        "(= C (as set.empty (FiniteSet Clock)))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((hi Pair)) (= (set.filter (lambda ((x Pair)) (<= (first x) (first hi))) P) P)) P) (as set.empty (FiniteSet Pair)))",
        "(= P (as set.empty (FiniteSet Pair)))");
    check_finite_set_simplification(
        "(= (set.filter (lambda ((hi Real)) (= (set.filter (lambda ((x Real)) (<= x hi)) R) R)) R) (as set.empty (FiniteSet Real)))",
        "(= R (as set.empty (FiniteSet Real)))");
    check_finite_set_simplification(
        "(forall ((U (FiniteSet Int))) (= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= x hi)) U) U)) U) (as set.empty (FiniteSet Int))))",
        "(forall ((U (FiniteSet Int))) (= U (as set.empty (FiniteSet Int))))");
    check_finite_set_simplification(
        "(forall ((c Int)) (= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= (* c x) (* c hi))) S) S)) S) (as set.empty (FiniteSet Int))))",
        "(forall ((c Int)) (= S (as set.empty (FiniteSet Int))))");

    char const* unchanged[] = {
        "(= (set.filter (lambda ((x Clock)) (and (>= (time x) c) (<= (time x) (+ c 1)))) C) (as set.empty (FiniteSet Clock)))",
        "(= (set.filter (lambda ((x Pair)) (= (first x) c)) P) (as set.empty (FiniteSet Pair)))",
        "(= (set.filter (lambda ((x Maybe)) (= (value x) c)) M) (as set.empty (FiniteSet Maybe)))",
        "(= (set.filter (lambda ((x Clock)) (= (time x) r)) C) (as set.empty (FiniteSet Clock)))",
        "(= (set.filter (lambda ((x Int)) (= x (f x))) S) (as set.empty (FiniteSet Int)))",
        "(= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= x hi)) T) T)) S) (as set.empty (FiniteSet Int)))",
        "(= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (< x hi)) S) S)) S) (as set.empty (FiniteSet Int)))",
        "(= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= (f x) (- (f hi) 1))) S) S)) S) (as set.empty (FiniteSet Int)))",
        "(= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= (h x hi) (h hi hi))) S) S)) S) (as set.empty (FiniteSet Int)))",
        "(= (set.filter (lambda ((hi Int)) (= (set.filter (lambda ((x Int)) (<= x hi)) S) S)) S) S)"
    };
    for (char const* input : unchanged)
        check_finite_set_simplification(input, input);
}

static void tst_finite_set_simplifier_state(bool proofs) {
    ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
    reg_decl_plugins(m);
    finite_set_util fs(m);
    arith_util arith(m);
    sort_ref ints(arith.mk_int(), m);
    sort_ref sets(fs.mk_finite_set_sort(ints), m);
    expr_ref s(m.mk_const("S", sets), m), b(m.mk_const("b", m.mk_bool_sort()), m);
    symbol name("x");
    sort* domain = ints;
    quantifier_ref predicate(m.mk_lambda(1, &domain, &name, b), m);
    expr_ref filtered(fs.mk_filter(predicate, s), m);
    expr_ref formula(m.mk_eq(filtered, s), m);
    expr_dependency_ref dep(m.mk_leaf(b), m);
    proof_ref pr(m.mk_asserted(formula), m);
    base_dependent_expr_state state(m);
    state.add(dependent_expr(m, formula, pr, dep));
    state.advance_qhead();
    state.add(dependent_expr(m, formula, pr, dep));
    finite_set_simplifier simplify(m, params_ref(), state);
    simplify.reduce();
    ENSURE(state[0].fml() == formula);
    if (proofs) {
        ENSURE(state[1].fml() == formula);
        ENSURE(state[1].pr() == pr.get());
        return;
    }
    ENSURE(state[1].fml() != formula);
    ENSURE(state[1].dep() == dep.get());
    expr_ref result(state[1].fml(), m);
    simplify.reduce();
    ENSURE(state[1].fml() == result);
}

static void tst_finite_set_tactic() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_tactic tactic = Z3_mk_tactic(ctx, "finite-set");
    Z3_tactic_inc_ref(ctx, tactic);
    Z3_solver base = Z3_mk_solver_from_tactic(ctx, tactic);
    Z3_solver_inc_ref(ctx, base);
    Z3_simplifier simplifier = Z3_mk_simplifier(ctx, "finite-set-simplify");
    Z3_simplifier_inc_ref(ctx, simplifier);
    Z3_solver solver = Z3_solver_add_simplifier(ctx, base, simplifier);
    Z3_solver_inc_ref(ctx, solver);
    Z3_solver_from_string(ctx, solver, R"(
        (declare-const S (FiniteSet Int))
        (assert (not (= (set.filter (lambda ((x Int)) (= x 5)) S)
                       (as set.empty (FiniteSet Int)))))
    )");
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_model model = Z3_solver_get_model(ctx, solver);
    Z3_model_inc_ref(ctx, model);
    Z3_ast_vector assertions = Z3_solver_get_assertions(ctx, solver);
    Z3_ast_vector_inc_ref(ctx, assertions);
    Z3_ast value = nullptr;
    ENSURE(Z3_model_eval(ctx, model, Z3_ast_vector_get(ctx, assertions, 0), true, &value));
    ENSURE(Z3_get_bool_value(ctx, Z3_simplify(ctx, value)) == Z3_L_TRUE);
    Z3_solver_push(ctx, solver);
    Z3_solver_assert(ctx, solver, Z3_mk_not(ctx, Z3_ast_vector_get(ctx, assertions, 0)));
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
    Z3_solver_pop(ctx, solver, 1);
    ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
    Z3_ast_vector_dec_ref(ctx, assertions);
    Z3_model_dec_ref(ctx, model);
    Z3_solver_dec_ref(ctx, solver);
    Z3_simplifier_dec_ref(ctx, simplifier);
    Z3_solver_dec_ref(ctx, base);

    Z3_solver core_solver = Z3_mk_solver_from_tactic(ctx, tactic);
    Z3_solver_inc_ref(ctx, core_solver);
    Z3_params params = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, params);
    Z3_params_set_bool(ctx, params, Z3_mk_string_symbol(ctx, "unsat_core"), true);
    Z3_solver_set_params(ctx, core_solver, params);
    Z3_ast_vector core_assertions = Z3_parse_smtlib2_string(ctx, R"(
        (declare-const CoreS (FiniteSet Int))
        (assert (not (= (set.filter (lambda ((x Int)) (= x 5)) CoreS)
                       (as set.empty (FiniteSet Int)))))
        (assert (not (set.in 5 CoreS)))
    )", 0, nullptr, nullptr, 0, nullptr, nullptr);
    Z3_ast_vector_inc_ref(ctx, core_assertions);
    for (unsigned i = 0; i < 2; ++i) {
        Z3_ast label = Z3_mk_const(ctx, Z3_mk_int_symbol(ctx, i), Z3_mk_bool_sort(ctx));
        Z3_solver_assert_and_track(ctx, core_solver, Z3_ast_vector_get(ctx, core_assertions, i), label);
    }
    ENSURE(Z3_solver_check(ctx, core_solver) == Z3_L_FALSE);
    ENSURE(Z3_ast_vector_size(ctx, Z3_solver_get_unsat_core(ctx, core_solver)) == 2);
    Z3_stats stats = Z3_solver_get_statistics(ctx, core_solver);
    Z3_stats_inc_ref(ctx, stats);
    bool invoked = false;
    for (unsigned i = 0; i < Z3_stats_size(ctx, stats); ++i)
        if (std::string(Z3_stats_get_key(ctx, stats, i)) == "finite-set-simplify-fixed-points")
            invoked |= Z3_stats_get_uint_value(ctx, stats, i) > 0;
    ENSURE(invoked);
    Z3_stats_dec_ref(ctx, stats);
    Z3_ast_vector_dec_ref(ctx, core_assertions);
    Z3_params_dec_ref(ctx, params);
    Z3_solver_dec_ref(ctx, core_solver);
    Z3_tactic_dec_ref(ctx, tactic);
    Z3_del_context(ctx);
}

void tst_finite_set() {
    tst_finite_set_basic();
    tst_finite_set_map_filter();
    tst_finite_set_is_value();
    tst_finite_set_is_fully_interp();
    tst_finite_set_sort_size();
    tst_finite_set_size_members();
    tst_finite_set_size_three_members();
    tst_finite_set_size_union_singletons();
    tst_finite_set_quantified_membership();
    tst_finite_set_lambda_filter();
    tst_finite_set_lambda_predicates(false);
    tst_finite_set_lambda_predicates(true);
    tst_finite_set_simplifier();
    tst_finite_set_simplifier_state(false);
    tst_finite_set_simplifier_state(true);
    tst_finite_set_tactic();
}
