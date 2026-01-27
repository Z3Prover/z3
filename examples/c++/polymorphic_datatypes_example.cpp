/**
 * Example demonstrating Z3_mk_polymorphic_datatypes API for mutually recursive polymorphic datatypes.
 * 
 * This example creates Tree<T> and Forest<T> datatypes:
 * - Tree<T> has constructor: mk-tree(value: T, children: Forest<T>)
 * - Forest<T> has constructors: empty() and cons(head: Tree<T>, tail: Forest<T>)
 */

#include <iostream>
#include "z3.h"

int main() {
    std::cout << "Polymorphic Recursive Datatypes Example\n\n";
    
    // Create context
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    // Create type parameter T
    Z3_symbol t_sym = Z3_mk_string_symbol(ctx, "T");
    Z3_sort t_var = Z3_mk_type_variable(ctx, t_sym);
    
    // Define datatype names
    Z3_symbol tree_name = Z3_mk_string_symbol(ctx, "Tree");
    Z3_symbol forest_name = Z3_mk_string_symbol(ctx, "Forest");
    
    // Create forward references for mutual recursion
    Z3_sort tree_ref = Z3_mk_datatype_sort(ctx, tree_name, 1, &t_var);
    Z3_sort forest_ref = Z3_mk_datatype_sort(ctx, forest_name, 1, &t_var);
    
    // Define Tree<T> constructor: mk-tree(value: T, children: Forest<T>)
    Z3_symbol mk_tree_sym = Z3_mk_string_symbol(ctx, "mk-tree");
    Z3_symbol is_tree_sym = Z3_mk_string_symbol(ctx, "is-tree");
    Z3_symbol value_sym = Z3_mk_string_symbol(ctx, "value");
    Z3_symbol children_sym = Z3_mk_string_symbol(ctx, "children");
    
    Z3_symbol tree_field_names[2] = {value_sym, children_sym};
    Z3_sort tree_field_sorts[2] = {t_var, forest_ref};
    unsigned tree_sort_refs[2] = {0, 0};  // Both use explicit sorts, not recursive refs
    
    Z3_constructor tree_con = Z3_mk_constructor(
        ctx, mk_tree_sym, is_tree_sym, 2, tree_field_names, tree_field_sorts, tree_sort_refs
    );
    
    // Define Forest<T> constructors
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
    Z3_sort forest_field_sorts[2] = {tree_ref, forest_ref};
    unsigned forest_sort_refs[2] = {0, 0};  // Both use explicit sorts, not recursive refs
    
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
    
    std::cout << "Created mutually recursive polymorphic datatypes:\n";
    std::cout << "  Tree<T>: " << Z3_sort_to_string(ctx, sorts[0]) << "\n";
    std::cout << "  Forest<T>: " << Z3_sort_to_string(ctx, sorts[1]) << "\n\n";
    
    // Clean up constructor lists
    Z3_del_constructor_list(ctx, tree_list);
    Z3_del_constructor_list(ctx, forest_list);
    Z3_del_constructor(ctx, tree_con);
    Z3_del_constructor(ctx, empty_con);
    Z3_del_constructor(ctx, cons_con);
    
    // Instantiate with concrete type Int
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort int_params[1] = {int_sort};
    
    Z3_sort tree_int = Z3_mk_datatype_sort(ctx, tree_name, 1, int_params);
    Z3_sort forest_int = Z3_mk_datatype_sort(ctx, forest_name, 1, int_params);
    
    std::cout << "Instantiated with Int:\n";
    std::cout << "  Tree<Int>: " << Z3_sort_to_string(ctx, tree_int) << "\n";
    std::cout << "  Forest<Int>: " << Z3_sort_to_string(ctx, forest_int) << "\n\n";
    
    // Get constructors
    Z3_func_decl mk_tree_int = Z3_get_datatype_sort_constructor(ctx, tree_int, 0);
    Z3_func_decl empty_int = Z3_get_datatype_sort_constructor(ctx, forest_int, 0);
    Z3_func_decl cons_int = Z3_get_datatype_sort_constructor(ctx, forest_int, 1);
    
    std::cout << "Constructors:\n";
    std::cout << "  mk-tree: " << Z3_func_decl_to_string(ctx, mk_tree_int) << "\n";
    std::cout << "  empty: " << Z3_func_decl_to_string(ctx, empty_int) << "\n";
    std::cout << "  cons: " << Z3_func_decl_to_string(ctx, cons_int) << "\n\n";
    
    // Create an empty forest
    Z3_ast empty_forest = Z3_mk_app(ctx, empty_int, 0, nullptr);
    std::cout << "Empty forest: " << Z3_ast_to_string(ctx, empty_forest) << "\n";
    
    // Create a tree with value 42 and empty children
    Z3_ast forty_two = Z3_mk_int(ctx, 42, int_sort);
    Z3_ast args[2] = {forty_two, empty_forest};
    Z3_ast tree = Z3_mk_app(ctx, mk_tree_int, 2, args);
    std::cout << "Tree with value 42: " << Z3_ast_to_string(ctx, tree) << "\n";
    
    // Get accessors and extract value
    Z3_func_decl value_acc = Z3_get_datatype_sort_constructor_accessor(ctx, tree_int, 0, 0);
    Z3_ast extracted_value = Z3_mk_app(ctx, value_acc, 1, &tree);
    std::cout << "Extracted value: " << Z3_ast_to_string(ctx, extracted_value) << "\n\n";
    
    // Verify the sort of extracted value is Int
    Z3_sort extracted_sort = Z3_get_sort(ctx, extracted_value);
    if (Z3_is_eq_sort(ctx, extracted_sort, int_sort)) {
        std::cout << "✓ Extracted value has correct sort (Int)\n";
    }
    
    // Verify the children accessor returns a Forest<Int>
    Z3_func_decl children_acc = Z3_get_datatype_sort_constructor_accessor(ctx, tree_int, 0, 1);
    Z3_ast extracted_children = Z3_mk_app(ctx, children_acc, 1, &tree);
    Z3_sort children_sort = Z3_get_sort(ctx, extracted_children);
    if (Z3_is_eq_sort(ctx, children_sort, forest_int)) {
        std::cout << "✓ Extracted children has correct sort (Forest<Int>)\n";
    }
    
    std::cout << "\nExample completed successfully!\n";
    
    Z3_del_context(ctx);
    return 0;
}
