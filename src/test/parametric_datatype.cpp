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

/**
 * Test Z3_mk_polymorphic_datatypes API for mutually recursive polymorphic datatypes.
 * 
 * This test demonstrates creating mutually recursive parametric datatypes Tree<T> and Forest<T>:
 * - Tree<T> has constructor mk-tree(value: T, children: Forest<T>)
 * - Forest<T> has constructors empty() and cons(head: Tree<T>, tail: Forest<T>)
 */
static void test_polymorphic_datatypes_api() {
    std::cout << "\ntest_polymorphic_datatypes_api\n";
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    // Create type variable T for polymorphic datatypes
    Z3_symbol t_sym = Z3_mk_string_symbol(ctx, "T");
    Z3_sort t_var = Z3_mk_type_variable(ctx, t_sym);
    
    // Define datatype names
    Z3_symbol tree_name = Z3_mk_string_symbol(ctx, "Tree");
    Z3_symbol forest_name = Z3_mk_string_symbol(ctx, "Forest");
    
    // Create forward references for mutual recursion
    // Tree has index 0, Forest has index 1
    Z3_sort tree_ref = Z3_mk_datatype_sort(ctx, tree_name, 1, &t_var);
    Z3_sort forest_ref = Z3_mk_datatype_sort(ctx, forest_name, 1, &t_var);
    
    // Define Tree<T> constructor: mk-tree(value: T, children: Forest<T>)
    Z3_symbol mk_tree_sym = Z3_mk_string_symbol(ctx, "mk-tree");
    Z3_symbol is_tree_sym = Z3_mk_string_symbol(ctx, "is-tree");
    Z3_symbol value_sym = Z3_mk_string_symbol(ctx, "value");
    Z3_symbol children_sym = Z3_mk_string_symbol(ctx, "children");
    
    Z3_symbol tree_field_names[2] = {value_sym, children_sym};
    Z3_sort tree_field_sorts[2] = {t_var, forest_ref};  // T and Forest<T>
    unsigned tree_sort_refs[2] = {0, 1};  // 0=not recursive, 1=reference to Forest (index 1)
    
    Z3_constructor tree_con = Z3_mk_constructor(
        ctx, mk_tree_sym, is_tree_sym, 2, tree_field_names, tree_field_sorts, tree_sort_refs
    );
    
    // Define Forest<T> constructors:
    // 1. empty()
    Z3_symbol empty_sym = Z3_mk_string_symbol(ctx, "empty");
    Z3_symbol is_empty_sym = Z3_mk_string_symbol(ctx, "is-empty");
    Z3_constructor empty_con = Z3_mk_constructor(
        ctx, empty_sym, is_empty_sym, 0, nullptr, nullptr, nullptr
    );
    
    // 2. cons(head: Tree<T>, tail: Forest<T>)
    Z3_symbol cons_sym = Z3_mk_string_symbol(ctx, "cons");
    Z3_symbol is_cons_sym = Z3_mk_string_symbol(ctx, "is-cons");
    Z3_symbol head_sym = Z3_mk_string_symbol(ctx, "head");
    Z3_symbol tail_sym = Z3_mk_string_symbol(ctx, "tail");
    
    Z3_symbol forest_field_names[2] = {head_sym, tail_sym};
    Z3_sort forest_field_sorts[2] = {tree_ref, forest_ref};  // Tree<T> and Forest<T>
    unsigned forest_sort_refs[2] = {0, 1};  // 0=reference to Tree (index 0), 1=reference to Forest (index 1)
    
    Z3_constructor cons_con = Z3_mk_constructor(
        ctx, cons_sym, is_cons_sym, 2, forest_field_names, forest_field_sorts, forest_sort_refs
    );
    
    // Create constructor lists
    Z3_constructor tree_constructors[1] = {tree_con};
    Z3_constructor forest_constructors[2] = {empty_con, cons_con};
    
    Z3_constructor_list tree_list = Z3_mk_constructor_list(ctx, 1, tree_constructors);
    Z3_constructor_list forest_list = Z3_mk_constructor_list(ctx, 2, forest_constructors);
    
    // Setup parameters for Z3_mk_polymorphic_datatypes
    Z3_symbol sort_names[2] = {tree_name, forest_name};
    unsigned num_params[2] = {1, 1};  // Both have one type parameter (T)
    Z3_sort const* type_params[2] = {&t_var, &t_var};
    Z3_sort sorts[2];
    Z3_constructor_list constructor_lists[2] = {tree_list, forest_list};
    
    // Create the mutually recursive polymorphic datatypes
    Z3_mk_polymorphic_datatypes(ctx, 2, sort_names, num_params, type_params, sorts, constructor_lists);
    
    std::cout << "Created mutually recursive polymorphic datatypes Tree<T> and Forest<T>\n";
    std::cout << "Tree sort: " << Z3_sort_to_string(ctx, sorts[0]) << "\n";
    std::cout << "Forest sort: " << Z3_sort_to_string(ctx, sorts[1]) << "\n";
    
    // Clean up constructor lists
    Z3_del_constructor_list(ctx, tree_list);
    Z3_del_constructor_list(ctx, forest_list);
    Z3_del_constructor(ctx, tree_con);
    Z3_del_constructor(ctx, empty_con);
    Z3_del_constructor(ctx, cons_con);
    
    // Now instantiate with concrete type Int
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort int_params[1] = {int_sort};
    
    Z3_sort tree_int = Z3_mk_datatype_sort(ctx, tree_name, 1, int_params);
    Z3_sort forest_int = Z3_mk_datatype_sort(ctx, forest_name, 1, int_params);
    
    std::cout << "Instantiated Tree<Int>: " << Z3_sort_to_string(ctx, tree_int) << "\n";
    std::cout << "Instantiated Forest<Int>: " << Z3_sort_to_string(ctx, forest_int) << "\n";
    
    // Get constructors from Tree<Int>
    Z3_func_decl mk_tree_int = Z3_get_datatype_sort_constructor(ctx, tree_int, 0);
    Z3_func_decl value_acc = Z3_get_datatype_sort_constructor_accessor(ctx, tree_int, 0, 0);
    Z3_func_decl children_acc = Z3_get_datatype_sort_constructor_accessor(ctx, tree_int, 0, 1);
    
    std::cout << "mk-tree constructor: " << Z3_func_decl_to_string(ctx, mk_tree_int) << "\n";
    
    // Get constructors from Forest<Int>
    Z3_func_decl empty_int = Z3_get_datatype_sort_constructor(ctx, forest_int, 0);
    Z3_func_decl cons_int = Z3_get_datatype_sort_constructor(ctx, forest_int, 1);
    
    // Create an empty forest
    Z3_ast empty_forest = Z3_mk_app(ctx, empty_int, 0, nullptr);
    std::cout << "Empty forest: " << Z3_ast_to_string(ctx, empty_forest) << "\n";
    
    // Create a tree with value 42 and empty forest as children
    Z3_ast forty_two = Z3_mk_int(ctx, 42, int_sort);
    Z3_ast args[2] = {forty_two, empty_forest};
    Z3_ast tree = Z3_mk_app(ctx, mk_tree_int, 2, args);
    std::cout << "Tree with value 42: " << Z3_ast_to_string(ctx, tree) << "\n";
    
    // Verify the accessor extracts the correct value
    Z3_ast extracted_value = Z3_mk_app(ctx, value_acc, 1, &tree);
    std::cout << "Extracted value: " << Z3_ast_to_string(ctx, extracted_value) << "\n";
    
    // Verify the sort of extracted value is Int
    Z3_sort extracted_sort = Z3_get_sort(ctx, extracted_value);
    ENSURE(Z3_is_eq_sort(ctx, extracted_sort, int_sort));
    
    // Verify the children accessor returns a Forest<Int>
    Z3_ast extracted_children = Z3_mk_app(ctx, children_acc, 1, &tree);
    Z3_sort children_sort = Z3_get_sort(ctx, extracted_children);
    std::cout << "Extracted children sort: " << Z3_sort_to_string(ctx, children_sort) << "\n";
    ENSURE(Z3_is_eq_sort(ctx, children_sort, forest_int));
    
    std::cout << "test_polymorphic_datatypes_api passed!\n";
    
    Z3_del_context(ctx);
}

void tst_parametric_datatype() {
    test_polymorphic_datatype_api();
    test_polymorphic_datatypes_api();
}
