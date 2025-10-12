/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    parametric_datatype.cpp

Abstract:

    Test parametric datatypes with type variables.

Author:

    Copilot 2025-10-12

--*/

#include "api/z3.h"
#include "util/util.h"
#include <iostream>

/**
 * Test polymorphic type variables with algebraic datatype definitions.
 * 
 * This test uses Z3_mk_type_variable to create polymorphic type parameters alpha and beta,
 * defines a generic pair datatype, then instantiates it with concrete types using
 * Z3_mk_datatype_sort with parameters.
 */
static void test_parametric_pair() {
    std::cout << "test_parametric_pair\n";
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    // Create type variables alpha and beta for polymorphic datatype
    Z3_symbol alpha_sym = Z3_mk_string_symbol(ctx, "alpha");
    Z3_symbol beta_sym = Z3_mk_string_symbol(ctx, "beta");
    Z3_sort alpha = Z3_mk_type_variable(ctx, alpha_sym);
    Z3_sort beta = Z3_mk_type_variable(ctx, beta_sym);
    
    // Define parametric pair datatype with constructor mk-pair(first: alpha, second: beta)
    Z3_symbol pair_name = Z3_mk_string_symbol(ctx, "pair");
    Z3_symbol mk_pair_name = Z3_mk_string_symbol(ctx, "mk-pair");
    Z3_symbol is_pair_name = Z3_mk_string_symbol(ctx, "is-pair");
    Z3_symbol first_name = Z3_mk_string_symbol(ctx, "first");
    Z3_symbol second_name = Z3_mk_string_symbol(ctx, "second");
    
    Z3_symbol field_names[2] = {first_name, second_name};
    Z3_sort field_sorts[2] = {alpha, beta};  // Use type variables
    unsigned sort_refs[2] = {0, 0};  // Not recursive references
    
    Z3_constructor mk_pair_con = Z3_mk_constructor(
        ctx, mk_pair_name, is_pair_name, 2, field_names, field_sorts, sort_refs
    );
    
    // Create the parametric datatype
    Z3_constructor constructors[1] = {mk_pair_con};
    Z3_sort pair = Z3_mk_datatype(ctx, pair_name, 1, constructors);
    
    Z3_del_constructor(ctx, mk_pair_con);
    
    std::cout << "Created parametric pair datatype\n";
    std::cout << "pair sort: " << Z3_sort_to_string(ctx, pair) << "\n";
    
    // Now instantiate the datatype with concrete types
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort real_sort = Z3_mk_real_sort(ctx);
    
    // Create (pair Int Real)
    Z3_sort params_int_real[2] = {int_sort, real_sort};
    Z3_sort pair_int_real = Z3_mk_datatype_sort(ctx, pair_name, 2, params_int_real);
    
    // Create (pair Real Int)
    Z3_sort params_real_int[2] = {real_sort, int_sort};
    Z3_sort pair_real_int = Z3_mk_datatype_sort(ctx, pair_name, 2, params_real_int);
    
    std::cout << "Instantiated pair with Int and Real\n";
    std::cout << "pair_int_real: " << Z3_sort_to_string(ctx, pair_int_real) << "\n";
    std::cout << "pair_real_int: " << Z3_sort_to_string(ctx, pair_real_int) << "\n";
    
    // Get constructors and accessors from the instantiated datatypes
    Z3_func_decl mk_pair_int_real = Z3_get_datatype_sort_constructor(ctx, pair_int_real, 0);
    Z3_func_decl first_int_real = Z3_get_datatype_sort_constructor_accessor(ctx, pair_int_real, 0, 0);
    Z3_func_decl second_int_real = Z3_get_datatype_sort_constructor_accessor(ctx, pair_int_real, 0, 1);
    
    Z3_func_decl mk_pair_real_int = Z3_get_datatype_sort_constructor(ctx, pair_real_int, 0);
    Z3_func_decl first_real_int = Z3_get_datatype_sort_constructor_accessor(ctx, pair_real_int, 0, 0);
    Z3_func_decl second_real_int = Z3_get_datatype_sort_constructor_accessor(ctx, pair_real_int, 0, 1);
    
    std::cout << "Got constructors and accessors from instantiated datatypes\n";
    
    // Create constants p1 : (pair Int Real) and p2 : (pair Real Int)
    Z3_symbol p1_sym = Z3_mk_string_symbol(ctx, "p1");
    Z3_symbol p2_sym = Z3_mk_string_symbol(ctx, "p2");
    Z3_ast p1 = Z3_mk_const(ctx, p1_sym, pair_int_real);
    Z3_ast p2 = Z3_mk_const(ctx, p2_sym, pair_real_int);
    
    // Create (first p1) - should be Int
    Z3_ast first_p1 = Z3_mk_app(ctx, first_int_real, 1, &p1);
    
    // Create (second p2) - should be Int  
    Z3_ast second_p2 = Z3_mk_app(ctx, second_real_int, 1, &p2);
    
    // Create the equality (= (first p1) (second p2))
    Z3_ast eq = Z3_mk_eq(ctx, first_p1, second_p2);
    
    std::cout << "Created term: " << Z3_ast_to_string(ctx, eq) << "\n";
    
    // Verify the term was created successfully
    ENSURE(eq != nullptr);
    
    // Check that first_p1 and second_p2 have the same sort (Int)
    Z3_sort first_p1_sort = Z3_get_sort(ctx, first_p1);
    Z3_sort second_p2_sort = Z3_get_sort(ctx, second_p2);
    
    std::cout << "Sort of (first p1): " << Z3_sort_to_string(ctx, first_p1_sort) << "\n";
    std::cout << "Sort of (second p2): " << Z3_sort_to_string(ctx, second_p2_sort) << "\n";
    
    // Both should be Int
    ENSURE(Z3_is_eq_sort(ctx, first_p1_sort, int_sort));
    ENSURE(Z3_is_eq_sort(ctx, second_p2_sort, int_sort));
    
    std::cout << "test_parametric_pair passed!\n";
    
    Z3_del_context(ctx);
}

void tst_parametric_datatype() {
    test_parametric_pair();
}
