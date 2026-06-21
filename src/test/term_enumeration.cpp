/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    tst_term_enumeration.cpp

Abstract:

    Test term enumeration module

--*/


#include "ast/rewriter/term_enumeration.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/obj_hashtable.h"
#include <iostream>
#include <sstream>

static void tst_basic_enumeration() {
    std::cout << "=== test basic enumeration ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    
    term_enumeration te(m);
    
    // Add some leaf productions (constants)
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    te.add_production(zero);
    te.add_production(one);
    
    // Enumerate terms of Int sort
    sort* int_sort = a.mk_int();
    unsigned count = 0;
    for (expr* e : te.enum_terms(int_sort)) {
        std::cout << "Term: " << mk_pp(e, m) << "\n";
        count++;
        if (count >= 5) break; // Limit output
    }
    
    ENSURE(count >= 2); // At least 0 and 1
    std::cout << "Enumerated " << count << " terms\n";
}

static void tst_enumeration_with_operators() {
    std::cout << "=== test enumeration with operators ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    
    term_enumeration te(m);
    
    // Add leaf productions
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    te.add_production(zero);
    te.add_production(one);
    
    // Add operator productions (+ and *)
    // Get func_decl by creating an app and extracting the decl
    app_ref tmp_add(a.mk_add(zero, one), m);
    app_ref tmp_mul(a.mk_mul(zero, one), m);
    func_decl* add_decl = tmp_add->get_decl();
    func_decl* mul_decl = tmp_mul->get_decl();
    te.add_production(add_decl);
    te.add_production(mul_decl);
    
    sort* int_sort = a.mk_int();
    unsigned count = 0;
    for (expr* e : te.enum_terms(int_sort)) {
        std::cout << "Term: " << mk_pp(e, m) << "\n";
        count++;
        if (count >= 20) break; // Limit output
    }
    
    ENSURE(count >= 2); // At least the leaves
    std::cout << "Enumerated " << count << " terms with operators\n";
}

static void tst_observational_equivalence_filter() {
    std::cout << "=== test observational equivalence filter ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    th_rewriter rw(m);

    term_enumeration te(m);

    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    te.add_production(zero);
    te.add_production(one);

    app_ref tmp_add(a.mk_add(zero, one), m);
    te.add_production(tmp_add->get_decl());

    sort* int_sort = a.mk_int();
    obj_hashtable<expr> seen;
    unsigned count = 0;
    for (expr* e : te.enum_terms(int_sort)) {
        expr_ref r(m);
        rw(e, r);
        ENSURE(r == e);
        ENSURE(!seen.contains(r));
        seen.insert(r);
        count++;
        if (count >= 20) break;
    }

    ENSURE(count >= 2);
}

static void tst_display() {
    std::cout << "=== test display ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    
    term_enumeration te(m);
    
    // Add leaf productions
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    te.add_production(zero);
    te.add_production(one);
    
    // Add operator productions
    app_ref tmp_add(a.mk_add(zero, one), m);
    func_decl* add_decl = tmp_add->get_decl();
    te.add_production(add_decl);
    
    sort* int_sort = a.mk_int();
    unsigned count = 0;
    for (expr* e : te.enum_terms(int_sort)) {
        (void)e;
        count++;
        if (count >= 10) break;
    }
    
    std::cout << "Internal state after enumeration:\n";
    std::ostringstream oss;
    te.display(oss);
    std::cout << oss.str();
    
    // Verify display produced some output
    ENSURE(!oss.str().empty());
}

static void tst_bitvector_enumeration() {
    std::cout << "=== test bitvector enumeration ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    
    term_enumeration te(m);
    
    // Add bitvector constants
    unsigned bv_size = 8;
    expr_ref bv_zero(bv.mk_numeral(0, bv_size), m);
    expr_ref bv_one(bv.mk_numeral(1, bv_size), m);
    te.add_production(bv_zero);
    te.add_production(bv_one);
    
    // Add bvadd operator
    app_ref tmp_add(bv.mk_bv_add(bv_zero, bv_one), m);
    func_decl* bvadd = tmp_add->get_decl();
    te.add_production(bvadd);
    
    sort* bv8 = bv.mk_sort(bv_size);
    unsigned count = 0;
    for (expr* e : te.enum_terms(bv8)) {
        std::cout << "BV Term: " << mk_pp(e, m) << "\n";
        count++;
        if (count >= 10) break;
    }
    
    ENSURE(count >= 2);
    std::cout << "Enumerated " << count << " bitvector terms\n";
}

static void tst_multiple_sorts() {
    std::cout << "=== test multiple sorts ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    
    term_enumeration te(m);
    
    // Add Int constants
    expr_ref i_zero(a.mk_int(0), m);
    expr_ref i_one(a.mk_int(1), m);
    te.add_production(i_zero);
    te.add_production(i_one);
    
    // Add Real constants  
    expr_ref r_zero(a.mk_real(0), m);
    expr_ref r_one(a.mk_real(1), m);
    te.add_production(r_zero);
    te.add_production(r_one);
    
    // Enumerate Int terms
    sort* int_sort = a.mk_int();
    unsigned int_count = 0;
    for (expr* e : te.enum_terms(int_sort)) {
        std::cout << "Int Term: " << mk_pp(e, m) << "\n";
        int_count++;
        if (int_count >= 5) break;
    }
    
    ENSURE(int_count >= 2);
    std::cout << "Enumerated " << int_count << " Int terms\n";
}

static void tst_nested_array_enumeration() {
    std::cout << "=== test nested array enumeration (Array(A, Array(B, A))) ===\n";
    ast_manager m;
    reg_decl_plugins(m);
    array_util arr(m);

    term_enumeration te(m);

    // Create uninterpreted sorts A and B
    sort_ref sort_A(m.mk_uninterpreted_sort(symbol("A")), m);
    sort_ref sort_B(m.mk_uninterpreted_sort(symbol("B")), m);

    // Create nested array sort: Array(B, A) - arrays indexed by B returning A
    sort_ref array_B_A(arr.mk_array_sort(sort_B, sort_A), m);

    // Create outer array sort: Array(A, Array(B, A)) - arrays indexed by A returning Array(B,A)
    sort_ref array_A_arrayBA(arr.mk_array_sort(sort_A, array_B_A), m);

    std::cout << "Sort A: " << mk_pp(sort_A.get(), m) << "\n";
    std::cout << "Sort B: " << mk_pp(sort_B.get(), m) << "\n";
    std::cout << "Sort Array(B, A): " << mk_pp(array_B_A.get(), m) << "\n";
    std::cout << "Sort Array(A, Array(B, A)): " << mk_pp(array_A_arrayBA.get(), m) << "\n";

    // Add constants of sort A
    app_ref a0(m.mk_const(symbol("a0"), sort_A), m);
    app_ref a1(m.mk_const(symbol("a1"), sort_A), m);
    te.add_production(a0);
    te.add_production(a1);

    // Add constants of sort B  
    app_ref b0(m.mk_const(symbol("b0"), sort_B), m);
    app_ref b1(m.mk_const(symbol("b1"), sort_B), m);
    te.add_production(b0);
    te.add_production(b1);

    // Add a constant array of inner type Array(B, A) - const_array(a0) : Array(B, A)
    app_ref const_inner(arr.mk_const_array(array_B_A, a0), m);
    te.add_production(const_inner);

    // Add a constant array of outer type Array(A, Array(B, A))
    app_ref const_outer(arr.mk_const_array(array_A_arrayBA, const_inner), m);
    te.add_production(const_outer);

    // Add store operator for the inner array type Array(B, A)
    // store(array, index, value) : store(Array(B,A), B, A) -> Array(B,A)
    expr* store_inner_args[3] = { const_inner.get(), b0.get(), a0.get() };
    app_ref tmp_store_inner(arr.mk_store(3, store_inner_args), m);
    func_decl* store_inner_decl = tmp_store_inner->get_decl();
    te.add_production(store_inner_decl);

    // Add store operator for the outer array type Array(A, Array(B, A))
    // store(array, index, value) : store(Array(A, Array(B,A)), A, Array(B,A)) -> Array(A, Array(B,A))
    expr* store_outer_args[3] = { const_outer.get(), a0.get(), const_inner.get() };
    app_ref tmp_store_outer(arr.mk_store(3, store_outer_args), m);
    func_decl* store_outer_decl = tmp_store_outer->get_decl();
    te.add_production(store_outer_decl);

    // Add select operator for the outer array (returns Array(B, A))
    // select(Array(A, Array(B,A)), A) -> Array(B, A)
    app_ref tmp_select_outer(arr.mk_select(const_outer.get(), a0.get()), m);
    func_decl* select_outer_decl = tmp_select_outer->get_decl();
    te.add_production(select_outer_decl);

    // Enumerate terms of the nested array sort Array(A, Array(B, A))
    std::cout << "\nEnumerating terms of sort Array(A, Array(B, A)):\n";
    unsigned count = 0;
    for (expr* e : te.enum_terms(array_A_arrayBA)) {
        std::cout << "  Term " << count << ": " << mk_pp(e, m) << "\n";
        count++;
        if (count >= 15) break; // Limit output
    }

    ENSURE(count >= 1); // At least the constant array
    std::cout << "Enumerated " << count << " terms of sort Array(A, Array(B, A))\n";

    te.display(std::cout);
}

void tst_term_enumeration() {
    tst_basic_enumeration();
    tst_enumeration_with_operators();
    tst_observational_equivalence_filter();
    tst_display();
    tst_bitvector_enumeration();
    tst_multiple_sorts();
    tst_nested_array_enumeration();
    std::cout << "All term_enumeration tests passed!\n";
}
