/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parser_context_example.c

Abstract:

    Example demonstrating the use of Z3_parser_context for incremental parsing.
    
    The Z3_parser_context API allows you to parse SMTLIB2 commands incrementally,
    maintaining state (declarations, assertions) between parse calls. This is useful
    for interactive applications or when processing commands in chunks.

Author:

    GitHub Copilot

--*/

#include<stdio.h>
#include<stdlib.h>
#include<z3.h>

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
    fprintf(stderr,"Error: %s.\n", message);
    exit(1);
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

/**
   \brief Create a logical context with model construction enabled.
*/
Z3_context mk_context()
{
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(ctx, error_handler);
    return ctx;
}

/**
   \brief Create a solver.
*/
Z3_solver mk_solver(Z3_context ctx)
{
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    return s;
}

/**
   \brief Delete a solver.
*/
void del_solver(Z3_context ctx, Z3_solver s)
{
    Z3_solver_dec_ref(ctx, s);
}

/**
   \brief Basic example of using Z3_parser_context.
   
   This example demonstrates:
   1. Creating a parser context
   2. Parsing declarations incrementally
   3. Parsing assertions incrementally
   4. Using the parsed formulas in a solver
*/
void parser_context_basic_example()
{
    printf("\n=== Basic Parser Context Example ===\n");
    
    Z3_context ctx = mk_context();
    Z3_parser_context parser = Z3_mk_parser_context(ctx);
    Z3_parser_context_inc_ref(ctx, parser);
    
    // First, declare some constants
    printf("Parsing declarations...\n");
    Z3_ast_vector decls = Z3_parser_context_from_string(ctx, parser, 
        "(declare-const x Int)\n"
        "(declare-const y Int)");
    Z3_ast_vector_inc_ref(ctx, decls);
    printf("Parsed %d formulas from declarations\n", Z3_ast_vector_size(ctx, decls));
    Z3_ast_vector_dec_ref(ctx, decls);
    
    // Now parse some assertions using the previously declared symbols
    printf("\nParsing first set of assertions...\n");
    Z3_ast_vector assertions1 = Z3_parser_context_from_string(ctx, parser,
        "(assert (> x 0))\n"
        "(assert (< y 10))");
    Z3_ast_vector_inc_ref(ctx, assertions1);
    
    printf("Got %d assertions:\n", Z3_ast_vector_size(ctx, assertions1));
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions1); i++) {
        Z3_ast assertion = Z3_ast_vector_get(ctx, assertions1, i);
        printf("  %s\n", Z3_ast_to_string(ctx, assertion));
    }
    
    // Parse more assertions incrementally
    printf("\nParsing second set of assertions...\n");
    Z3_ast_vector assertions2 = Z3_parser_context_from_string(ctx, parser,
        "(assert (< x y))");
    Z3_ast_vector_inc_ref(ctx, assertions2);
    
    printf("Got %d more assertion:\n", Z3_ast_vector_size(ctx, assertions2));
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions2); i++) {
        Z3_ast assertion = Z3_ast_vector_get(ctx, assertions2, i);
        printf("  %s\n", Z3_ast_to_string(ctx, assertion));
    }
    
    // Now use these assertions in a solver
    printf("\nSolving the constraints...\n");
    Z3_solver solver = mk_solver(ctx);
    
    // Add all assertions to the solver
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions1); i++) {
        Z3_solver_assert(ctx, solver, Z3_ast_vector_get(ctx, assertions1, i));
    }
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions2); i++) {
        Z3_solver_assert(ctx, solver, Z3_ast_vector_get(ctx, assertions2, i));
    }
    
    Z3_lbool result = Z3_solver_check(ctx, solver);
    if (result == Z3_L_TRUE) {
        printf("SAT\n");
        Z3_model model = Z3_solver_get_model(ctx, solver);
        Z3_model_inc_ref(ctx, model);
        printf("Model:\n%s\n", Z3_model_to_string(ctx, model));
        Z3_model_dec_ref(ctx, model);
    } else if (result == Z3_L_FALSE) {
        printf("UNSAT\n");
    } else {
        printf("UNKNOWN\n");
    }
    
    // Cleanup
    del_solver(ctx, solver);
    Z3_ast_vector_dec_ref(ctx, assertions2);
    Z3_ast_vector_dec_ref(ctx, assertions1);
    Z3_parser_context_dec_ref(ctx, parser);
    Z3_del_context(ctx);
}

/**
   \brief Example showing how to add custom sorts and declarations to parser context.
   
   This demonstrates using Z3_parser_context_add_sort and Z3_parser_context_add_decl
   to make external symbols available to the parser.
*/
void parser_context_custom_decls_example()
{
    printf("\n=== Parser Context with Custom Declarations Example ===\n");
    
    Z3_context ctx = mk_context();
    Z3_parser_context parser = Z3_mk_parser_context(ctx);
    Z3_parser_context_inc_ref(ctx, parser);
    
    // Create a custom sort programmatically
    Z3_symbol color_name = Z3_mk_string_symbol(ctx, "Color");
    Z3_sort color_sort = Z3_mk_uninterpreted_sort(ctx, color_name);
    
    // Add the sort to the parser context
    printf("Adding custom sort 'Color' to parser context...\n");
    Z3_parser_context_add_sort(ctx, parser, color_sort);
    
    // Create a custom function declaration programmatically
    Z3_symbol is_red_name = Z3_mk_string_symbol(ctx, "is_red");
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_func_decl is_red = Z3_mk_func_decl(ctx, is_red_name, 1, &color_sort, bool_sort);
    
    // Add the function to the parser context
    printf("Adding custom function 'is_red' to parser context...\n");
    Z3_parser_context_add_decl(ctx, parser, is_red);
    
    // Now we can parse SMTLIB2 strings that use these custom symbols
    printf("\nParsing with custom symbols...\n");
    Z3_ast_vector formulas = Z3_parser_context_from_string(ctx, parser,
        "(declare-const c1 Color)\n"
        "(declare-const c2 Color)\n"
        "(assert (is_red c1))\n"
        "(assert (not (is_red c2)))");
    Z3_ast_vector_inc_ref(ctx, formulas);
    
    printf("Parsed %d formulas:\n", Z3_ast_vector_size(ctx, formulas));
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, formulas); i++) {
        Z3_ast formula = Z3_ast_vector_get(ctx, formulas, i);
        printf("  %s\n", Z3_ast_to_string(ctx, formula));
    }
    
    // Cleanup
    Z3_ast_vector_dec_ref(ctx, formulas);
    Z3_parser_context_dec_ref(ctx, parser);
    Z3_del_context(ctx);
}

/**
   \brief Example demonstrating declaration and usage patterns.
   
   Shows how to declare symbols explicitly before using them.
*/
void parser_context_declarations_example()
{
    printf("\n=== Parser Context Declarations Example ===\n");
    
    Z3_context ctx = mk_context();
    Z3_parser_context parser = Z3_mk_parser_context(ctx);
    Z3_parser_context_inc_ref(ctx, parser);
    
    // First, explicitly declare constants
    printf("Explicitly declaring constants 'a' and 'b'...\n");
    Z3_ast_vector decls = Z3_parser_context_from_string(ctx, parser,
        "(declare-const a Int)\n"
        "(declare-const b Int)");
    Z3_ast_vector_inc_ref(ctx, decls);
    printf("Declarations parsed successfully\n");
    Z3_ast_vector_dec_ref(ctx, decls);
    
    // Now use the declared constants
    printf("\nParsing assertions using declared constants...\n");
    Z3_ast_vector formulas = Z3_parser_context_from_string(ctx, parser,
        "(assert (> a 5))\n"
        "(assert (< b 10))");
    
    Z3_ast_vector_inc_ref(ctx, formulas);
    printf("Successfully parsed %d assertions:\n", Z3_ast_vector_size(ctx, formulas));
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, formulas); i++) {
        printf("  %s\n", Z3_ast_to_string(ctx, Z3_ast_vector_get(ctx, formulas, 0)));
    }
    Z3_ast_vector_dec_ref(ctx, formulas);
    
    // Cleanup
    Z3_parser_context_dec_ref(ctx, parser);
    Z3_del_context(ctx);
}

/**
   \brief Main function demonstrating all parser context examples.
*/
int main()
{
    printf("Z3 Parser Context Examples\n");
    printf("==========================\n");
    printf("\nThese examples demonstrate the Z3_parser_context API,\n");
    printf("which allows incremental parsing of SMTLIB2 commands.\n");
    
    parser_context_basic_example();
    parser_context_custom_decls_example();
    parser_context_declarations_example();
    
    printf("\n=== All examples completed successfully ===\n");
    
    return 0;
}
