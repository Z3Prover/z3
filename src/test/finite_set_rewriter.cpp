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
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/finite_set_rewriter.h"

class finite_set_rewriter_test {
public:
    void test_union_idempotent() {
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
        app_ref union_app(fsets.mk_union(s1, s1), m);
        expr_ref result(m);
        br_status st = rw.mk_app_core(union_app->get_decl(), union_app->get_num_args(), union_app->get_args(), result);

        ENSURE(st == BR_DONE);
        ENSURE(result == s1);
    }

    void test_intersect_idempotent() {
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
        app_ref intersect_app(fsets.mk_intersect(s1, s1), m);
        expr_ref result(m);
        br_status st =
            rw.mk_app_core(intersect_app->get_decl(), intersect_app->get_num_args(), intersect_app->get_args(), result);

        ENSURE(st == BR_DONE);
        ENSURE(result == s1);
    }

    void test_difference_same() {
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
        app_ref diff_app(fsets.mk_difference(s1, s1), m);
        expr_ref result(m);
        br_status st = rw.mk_app_core(diff_app->get_decl(), diff_app->get_num_args(), diff_app->get_args(), result);

        ENSURE(st == BR_DONE);
        ENSURE(fsets.is_empty(result));
    }

    void test_subset_rewrite() {
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
        app_ref subset_app(fsets.mk_subset(s1, s2), m);
        expr_ref result(m);
        br_status st =
            rw.mk_app_core(subset_app->get_decl(), subset_app->get_num_args(), subset_app->get_args(), result);

        ENSURE(st == BR_REWRITE3);
        ENSURE(m.is_eq(result));

        // Check that result is an equality
        app *eq = to_app(result);
        ENSURE(eq->get_num_args() == 2);

        // The left side should be set.intersect(s1, s2)
        expr *lhs = eq->get_arg(0);
        ENSURE(fsets.is_intersect(lhs));

        // The right side should be s1
        expr *rhs = eq->get_arg(1);
        ENSURE(rhs == s1);
    }

    void test_mk_app_core() {
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

    void test_union_with_empty() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);

        // Create a set and empty set
        sort_ref int_sort(arith.mk_int(), m);
        expr_ref zero(arith.mk_int(0), m);
        expr_ref ten(arith.mk_int(10), m);
        app_ref s1(fsets.mk_range(zero, ten), m);
        app_ref empty_set(fsets.mk_empty(s1->get_sort()), m);

        // Test set.union(s1, empty) -> s1
        app_ref union_app1(fsets.mk_union(s1, empty_set), m);
        expr_ref result1(m);
        br_status st1 =
            rw.mk_app_core(union_app1->get_decl(), union_app1->get_num_args(), union_app1->get_args(), result1);
        ENSURE(st1 == BR_DONE);
        ENSURE(result1 == s1);

        // Test set.union(empty, s1) -> s1
        app_ref union_app2(fsets.mk_union(empty_set, s1), m);
        expr_ref result2(m);
        br_status st2 =
            rw.mk_app_core(union_app2->get_decl(), union_app2->get_num_args(), union_app2->get_args(), result2);
        ENSURE(st2 == BR_DONE);
        ENSURE(result2 == s1);
    }

    void test_intersect_with_empty() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);

        // Create a set and empty set
        sort_ref int_sort(arith.mk_int(), m);
        expr_ref zero(arith.mk_int(0), m);
        expr_ref ten(arith.mk_int(10), m);
        app_ref s1(fsets.mk_range(zero, ten), m);
        app_ref empty_set(fsets.mk_empty(s1->get_sort()), m);

        // Test set.intersect(s1, empty) -> empty
        app_ref intersect_app1(fsets.mk_intersect(s1, empty_set), m);
        expr_ref result1(m);
        br_status st1 = rw.mk_app_core(intersect_app1->get_decl(), intersect_app1->get_num_args(),
                                       intersect_app1->get_args(), result1);
        ENSURE(st1 == BR_DONE);
        ENSURE(result1 == empty_set);

        // Test set.intersect(empty, s1) -> empty
        app_ref intersect_app2(fsets.mk_intersect(empty_set, s1), m);
        expr_ref result2(m);
        br_status st2 = rw.mk_app_core(intersect_app2->get_decl(), intersect_app2->get_num_args(),
                                       intersect_app2->get_args(), result2);
        ENSURE(st2 == BR_DONE);
        ENSURE(result2 == empty_set);
    }

    void test_difference_with_empty() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);

        // Create a set and empty set
        sort_ref int_sort(arith.mk_int(), m);
        expr_ref zero(arith.mk_int(0), m);
        expr_ref ten(arith.mk_int(10), m);
        app_ref s1(fsets.mk_range(zero, ten), m);
        app_ref empty_set(fsets.mk_empty(s1->get_sort()), m);

        // Test set.difference(s1, empty) -> s1
        app_ref diff_app1(fsets.mk_difference(s1, empty_set), m);
        expr_ref result1(m);
        br_status st1 =
            rw.mk_app_core(diff_app1->get_decl(), diff_app1->get_num_args(), diff_app1->get_args(), result1);
        ENSURE(st1 == BR_DONE);
        ENSURE(result1 == s1);

        // Test set.difference(empty, s1) -> empty
        app_ref diff_app2(fsets.mk_difference(empty_set, s1), m);
        expr_ref result2(m);
        br_status st2 =
            rw.mk_app_core(diff_app2->get_decl(), diff_app2->get_num_args(), diff_app2->get_args(), result2);
        ENSURE(st2 == BR_DONE);
        ENSURE(result2 == empty_set);
    }

    void test_subset_with_empty() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);

        // Create a set and empty set
        sort_ref int_sort(arith.mk_int(), m);
        expr_ref zero(arith.mk_int(0), m);
        expr_ref ten(arith.mk_int(10), m);
        app_ref s1(fsets.mk_range(zero, ten), m);
        app_ref empty_set(fsets.mk_empty(s1->get_sort()), m);

        // Test set.subset(empty, s1) -> true
        app_ref subset_app1(fsets.mk_subset(empty_set, s1), m);
        expr_ref result1(m);
        br_status st1 =
            rw.mk_app_core(subset_app1->get_decl(), subset_app1->get_num_args(), subset_app1->get_args(), result1);
        ENSURE(st1 == BR_DONE);
        ENSURE(m.is_true(result1));

        // Test set.subset(s1, s1) -> true
        app_ref subset_app2(fsets.mk_subset(s1, s1), m);
        expr_ref result2(m);
        br_status st2 =
            rw.mk_app_core(subset_app2->get_decl(), subset_app2->get_num_args(), subset_app2->get_args(), result2);
        ENSURE(st2 == BR_DONE);
        ENSURE(m.is_true(result2));
    }

    void test_in_singleton() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);

        // Create elements and singleton
        expr_ref five(arith.mk_int(5), m);
        expr_ref ten(arith.mk_int(10), m);
        app_ref singleton_five(fsets.mk_singleton(five), m);

        // Test set.in(five, singleton(five)) -> true
        app_ref in_app1(fsets.mk_in(five, singleton_five), m);
        expr_ref result1(m);
        br_status st1 = rw.mk_app_core(in_app1->get_decl(), in_app1->get_num_args(), in_app1->get_args(), result1);
        ENSURE(st1 == BR_DONE);
        ENSURE(m.is_true(result1));

        // Test set.in(ten, singleton(five)) -> ten = five
        app_ref in_app2(fsets.mk_in(ten, singleton_five), m);
        expr_ref result2(m);
        br_status st2 = rw.mk_app_core(in_app2->get_decl(), in_app2->get_num_args(), in_app2->get_args(), result2);
        ENSURE(st2 == BR_REWRITE1);
        ENSURE(m.is_eq(result2));
    }

    void test_in_empty() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);

        // Create element and empty set
        sort_ref int_sort(arith.mk_int(), m);
        expr_ref five(arith.mk_int(5), m);
        parameter param(int_sort.get());
        sort_ref set_sort(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &param), m);
        app_ref empty_set(fsets.mk_empty(set_sort), m);

        // Test set.in(five, empty) -> false
        app_ref in_app(fsets.mk_in(five, empty_set), m);
        expr_ref result(m);
        br_status st = rw.mk_app_core(in_app->get_decl(), in_app->get_num_args(), in_app->get_args(), result);
        ENSURE(st == BR_DONE);
        ENSURE(m.is_false(result));
    }
    void test_map_filter() {
        ast_manager m;
        reg_decl_plugins(m);

        finite_set_util fsets(m);
        finite_set_rewriter rw(m);
        arith_util arith(m);
        array_util autil(m);

        sort_ref int_sort(arith.mk_int(), m);
        parameter param(int_sort.get());
        sort_ref set_sort(m.mk_sort(fsets.get_family_id(), FINITE_SET_SORT, 1, &param), m);
        sort *domain[1] = { int_sort.get() };
        sort_ref array_sort(autil.mk_array_sort(1, domain, int_sort), m);
        sort_ref pred_sort(autil.mk_array_sort(1, domain, m.mk_bool_sort()), m);
        expr_ref f(m.mk_const(symbol("f"), array_sort), m);
        expr_ref p(m.mk_const(symbol("p"), pred_sort), m);
        expr_ref five(arith.mk_int(5), m);
        expr_ref ten(arith.mk_int(10), m);
        app_ref empty_set(fsets.mk_empty(set_sort), m);
        app_ref singleton_five(fsets.mk_singleton(five), m);
        app_ref singleton_ten(fsets.mk_singleton(ten), m);

        // set.map(f, empty) -> empty
        app_ref map1(fsets.mk_map(f, empty_set), m);
        expr_ref result(m);
        br_status st = rw.mk_app_core(map1->get_decl(), map1->get_num_args(), map1->get_args(), result);
        ENSURE(st == BR_DONE);
        ENSURE(fsets.is_empty(result));

        // set.map(f, singleton(5)) -> singleton(f[5])
        app_ref map2(fsets.mk_map(f, singleton_five), m);
        st = rw.mk_app_core(map2->get_decl(), map2->get_num_args(), map2->get_args(), result);
        ENSURE(st == BR_REWRITE_FULL);
        ENSURE(result == fsets.mk_singleton(autil.mk_select(f, five)));

        // set.map(f, union(s, t)) -> union(map(f, s), map(f, t))
        app_ref union_set(fsets.mk_union(singleton_five, singleton_ten), m);
        app_ref map3(fsets.mk_map(f, union_set), m);
        st = rw.mk_app_core(map3->get_decl(), map3->get_num_args(), map3->get_args(), result);
        ENSURE(st == BR_REWRITE_FULL);
        ENSURE(fsets.is_union(result));

        // set.filter(p, empty) -> empty
        app_ref filter1(fsets.mk_filter(p, empty_set), m);
        st = rw.mk_app_core(filter1->get_decl(), filter1->get_num_args(), filter1->get_args(), result);
        ENSURE(st == BR_DONE);
        ENSURE(result == empty_set);

        // set.filter(p, singleton(5)) -> ite(p[5], singleton(5), empty)
        app_ref filter2(fsets.mk_filter(p, singleton_five), m);
        st = rw.mk_app_core(filter2->get_decl(), filter2->get_num_args(), filter2->get_args(), result);
        ENSURE(st == BR_REWRITE_FULL);
        ENSURE(m.is_ite(result));

        // set.filter(p, union(s, t)) -> union(filter(p, s), filter(p, t))
        app_ref filter3(fsets.mk_filter(p, union_set), m);
        st = rw.mk_app_core(filter3->get_decl(), filter3->get_num_args(), filter3->get_args(), result);
        ENSURE(st == BR_REWRITE_FULL);
        ENSURE(fsets.is_union(result));
    }
};

void tst_finite_set_rewriter() {
    finite_set_rewriter_test test;
    test.test_union_idempotent();
    test.test_intersect_idempotent();
    test.test_difference_same();
    test.test_subset_rewrite();
    test.test_mk_app_core();
    test.test_union_with_empty();
    test.test_intersect_with_empty();
    test.test_difference_with_empty();
    test.test_subset_with_empty();
    test.test_in_singleton();
    test.test_in_empty();
    test.test_map_filter();
}
