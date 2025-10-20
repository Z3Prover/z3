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
 * Test Z3_mk_polymorphic_datatype API with explicit parameters.
 * 
 * This test demonstrates the API that explicitly accepts type parameters.
 */
static void test_polymorphic_datatype_api() {
    std::cout << "test_polymorphic_datatype_api\n";
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    // Create type variables alpha and beta for polymorphic datatype
    Z3_symbol alpha_sym = Z3_mk_string_symbol(ctx, "alpha");
    Z3_symbol beta_sym = Z3_mk_string_symbol(ctx, "beta");
    Z3_sort alpha = Z3_mk_type_variable(ctx, alpha_sym);
    Z3_sort beta = Z3_mk_type_variable(ctx, beta_sym);
    
    // Define parametric triple datatype with constructor mk-triple(first: alpha, second: beta, third: alpha)
    Z3_symbol triple_name = Z3_mk_string_symbol(ctx, "triple");
    Z3_symbol mk_triple_name = Z3_mk_string_symbol(ctx, "mk-triple");
    Z3_symbol is_triple_name = Z3_mk_string_symbol(ctx, "is-triple");
    Z3_symbol first_name = Z3_mk_string_symbol(ctx, "first");
    Z3_symbol second_name = Z3_mk_string_symbol(ctx, "second");
    Z3_symbol third_name = Z3_mk_string_symbol(ctx, "third");
    
    Z3_symbol field_names[3] = {first_name, second_name, third_name};
    Z3_sort field_sorts[3] = {alpha, beta, alpha};  // Use type variables
    unsigned sort_refs[3] = {0, 0, 0};  // Not recursive references
    
    Z3_constructor mk_triple_con = Z3_mk_constructor(
        ctx, mk_triple_name, is_triple_name, 3, field_names, field_sorts, sort_refs
    );
    
    // Create the parametric datatype using Z3_mk_polymorphic_datatype
    Z3_constructor constructors[1] = {mk_triple_con};
    Z3_sort type_params[2] = {alpha, beta};
    Z3_sort triple = Z3_mk_polymorphic_datatype(ctx, triple_name, 2, type_params, 1, constructors);
    
    Z3_del_constructor(ctx, mk_triple_con);
    
    std::cout << "Created parametric triple datatype using Z3_mk_polymorphic_datatype\n";
    std::cout << "triple sort: " << Z3_sort_to_string(ctx, triple) << "\n";
    
    // Now instantiate the datatype with concrete types
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    
    // Create (triple Int Bool)
    Z3_sort params_int_bool[2] = {int_sort, bool_sort};
    Z3_sort triple_int_bool = Z3_mk_datatype_sort(ctx, triple_name, 2, params_int_bool);
    
    std::cout << "Instantiated triple with Int and Bool\n";
    std::cout << "triple_int_bool: " << Z3_sort_to_string(ctx, triple_int_bool) << "\n";
    
    // Get constructors and accessors from the instantiated datatype
    Z3_func_decl mk_triple_int_bool = Z3_get_datatype_sort_constructor(ctx, triple_int_bool, 0);
    Z3_func_decl first_int_bool = Z3_get_datatype_sort_constructor_accessor(ctx, triple_int_bool, 0, 0);
    Z3_func_decl second_int_bool = Z3_get_datatype_sort_constructor_accessor(ctx, triple_int_bool, 0, 1);
    Z3_func_decl third_int_bool = Z3_get_datatype_sort_constructor_accessor(ctx, triple_int_bool, 0, 2);
    
    std::cout << "Got constructors and accessors from instantiated datatype\n";
    
    // Create a constant t : (triple Int Bool)
    Z3_symbol t_sym = Z3_mk_string_symbol(ctx, "t");
    Z3_ast t = Z3_mk_const(ctx, t_sym, triple_int_bool);
    
    // Create (first t) - should be Int
    Z3_ast first_t = Z3_mk_app(ctx, first_int_bool, 1, &t);
    
    // Create (third t) - should also be Int
    Z3_ast third_t = Z3_mk_app(ctx, third_int_bool, 1, &t);
    
    // Create the equality (= (first t) (third t))
    Z3_ast eq = Z3_mk_eq(ctx, first_t, third_t);
    
    std::cout << "Created term: " << Z3_ast_to_string(ctx, eq) << "\n";
    
    // Verify the term was created successfully
    ENSURE(eq != nullptr);
    
    // Check that first_t and third_t have the same sort (Int)
    Z3_sort first_t_sort = Z3_get_sort(ctx, first_t);
    Z3_sort third_t_sort = Z3_get_sort(ctx, third_t);
    
    std::cout << "Sort of (first t): " << Z3_sort_to_string(ctx, first_t_sort) << "\n";
    std::cout << "Sort of (third t): " << Z3_sort_to_string(ctx, third_t_sort) << "\n";
    
    // Both should be Int
    ENSURE(Z3_is_eq_sort(ctx, first_t_sort, int_sort));
    ENSURE(Z3_is_eq_sort(ctx, third_t_sort, int_sort));
    
    std::cout << "test_polymorphic_datatype_api passed!\n";
    
    Z3_del_context(ctx);
}

void tst_parametric_datatype() {
    test_polymorphic_datatype_api();
}
