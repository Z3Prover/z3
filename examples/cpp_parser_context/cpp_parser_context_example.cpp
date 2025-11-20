/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parser_context_example.cpp

Abstract:

    Example demonstrating the use of Z3_parser_context for incremental parsing.
    
    The Z3_parser_context API allows you to parse SMTLIB2 commands incrementally,
    maintaining state (declarations, assertions) between parse calls. This is useful
    for interactive applications or when processing commands in chunks.

Author:

    GitHub Copilot

--*/

#include <iostream>
#include <z3.h>

/**
   \brief Helper class to manage Z3_parser_context lifecycle.
   
   Since there is no C++ wrapper for Z3_parser_context in z3++.h,
   this class provides RAII-style management.
*/
class parser_context {
    Z3_context m_ctx;
    Z3_parser_context m_parser;
    
public:
    parser_context(Z3_context ctx) : m_ctx(ctx) {
        m_parser = Z3_mk_parser_context(ctx);
        Z3_parser_context_inc_ref(ctx, m_parser);
    }
    
    ~parser_context() {
        Z3_parser_context_dec_ref(m_ctx, m_parser);
    }
    
    // Delete copy constructor and assignment operator
    parser_context(const parser_context&) = delete;
    parser_context& operator=(const parser_context&) = delete;
    
    operator Z3_parser_context() const { return m_parser; }
    
    /**
       \brief Parse a string of SMTLIB2 commands.
    */
    Z3_ast_vector parse_string(const char* str) {
        return Z3_parser_context_from_string(m_ctx, m_parser, str);
    }
    
    /**
       \brief Add a sort to the parser context.
    */
    void add_sort(Z3_sort s) {
        Z3_parser_context_add_sort(m_ctx, m_parser, s);
    }
    
    /**
       \brief Add a function declaration to the parser context.
    */
    void add_decl(Z3_func_decl f) {
        Z3_parser_context_add_decl(m_ctx, m_parser, f);
    }
};

/**
   \brief Helper class to manage Z3_ast_vector lifecycle.
*/
class ast_vector {
    Z3_context m_ctx;
    Z3_ast_vector m_vec;
    
public:
    ast_vector(Z3_context ctx, Z3_ast_vector vec) : m_ctx(ctx), m_vec(vec) {
        Z3_ast_vector_inc_ref(ctx, vec);
    }
    
    ~ast_vector() {
        Z3_ast_vector_dec_ref(m_ctx, m_vec);
    }
    
    // Delete copy constructor and assignment operator
    ast_vector(const ast_vector&) = delete;
    ast_vector& operator=(const ast_vector&) = delete;
    
    operator Z3_ast_vector() const { return m_vec; }
    
    unsigned size() const {
        return Z3_ast_vector_size(m_ctx, m_vec);
    }
    
    Z3_ast get(unsigned i) const {
        return Z3_ast_vector_get(m_ctx, m_vec, i);
    }
};

/**
   \brief Basic example of using Z3_parser_context.
   
   This example demonstrates:
   1. Creating a parser context
   2. Parsing declarations incrementally
   3. Parsing assertions incrementally
   4. Using the parsed formulas in a solver
*/
void parser_context_basic_example() {
    std::cout << "\n=== Basic Parser Context Example ===" << std::endl;
    
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    {
        parser_context parser(ctx);
        
        // First, declare some constants
        std::cout << "Parsing declarations..." << std::endl;
        {
            ast_vector decls(ctx, parser.parse_string(
                "(declare-const x Int)\n"
                "(declare-const y Int)"));
            std::cout << "Parsed " << decls.size() << " formulas from declarations" << std::endl;
        }
        
        // Now parse some assertions using the previously declared symbols
        std::cout << "\nParsing first set of assertions..." << std::endl;
        ast_vector assertions1(ctx, parser.parse_string(
            "(assert (> x 0))\n"
            "(assert (< y 10))"));
        
        std::cout << "Got " << assertions1.size() << " assertions:" << std::endl;
        for (unsigned i = 0; i < assertions1.size(); i++) {
            std::cout << "  " << Z3_ast_to_string(ctx, assertions1.get(i)) << std::endl;
        }
        
        // Parse more assertions incrementally
        std::cout << "\nParsing second set of assertions..." << std::endl;
        ast_vector assertions2(ctx, parser.parse_string(
            "(assert (< x y))"));
        
        std::cout << "Got " << assertions2.size() << " more assertion:" << std::endl;
        for (unsigned i = 0; i < assertions2.size(); i++) {
            std::cout << "  " << Z3_ast_to_string(ctx, assertions2.get(i)) << std::endl;
        }
        
        // Now use these assertions in a solver
        std::cout << "\nSolving the constraints..." << std::endl;
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        
        // Add all assertions to the solver
        for (unsigned i = 0; i < assertions1.size(); i++) {
            Z3_solver_assert(ctx, solver, assertions1.get(i));
        }
        for (unsigned i = 0; i < assertions2.size(); i++) {
            Z3_solver_assert(ctx, solver, assertions2.get(i));
        }
        
        Z3_lbool result = Z3_solver_check(ctx, solver);
        if (result == Z3_L_TRUE) {
            std::cout << "SAT" << std::endl;
            Z3_model model = Z3_solver_get_model(ctx, solver);
            Z3_model_inc_ref(ctx, model);
            std::cout << "Model:\n" << Z3_model_to_string(ctx, model) << std::endl;
            Z3_model_dec_ref(ctx, model);
        } else if (result == Z3_L_FALSE) {
            std::cout << "UNSAT" << std::endl;
        } else {
            std::cout << "UNKNOWN" << std::endl;
        }
        
        // Cleanup
        Z3_solver_dec_ref(ctx, solver);
    } // parser and vectors destructors run here
    
    Z3_del_context(ctx);
}

/**
   \brief Example showing how to add custom sorts and declarations to parser context.
   
   This demonstrates using Z3_parser_context_add_sort and Z3_parser_context_add_decl
   to make external symbols available to the parser.
*/
void parser_context_custom_decls_example() {
    std::cout << "\n=== Parser Context with Custom Declarations Example ===" << std::endl;
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    {
        parser_context parser(ctx);
        
        // Create a custom sort programmatically
        Z3_symbol color_name = Z3_mk_string_symbol(ctx, "Color");
        Z3_sort color_sort = Z3_mk_uninterpreted_sort(ctx, color_name);
        
        // Add the sort to the parser context
        std::cout << "Adding custom sort 'Color' to parser context..." << std::endl;
        parser.add_sort(color_sort);
        
        // Create a custom function declaration programmatically
        Z3_symbol is_red_name = Z3_mk_string_symbol(ctx, "is_red");
        Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
        Z3_func_decl is_red = Z3_mk_func_decl(ctx, is_red_name, 1, &color_sort, bool_sort);
        
        // Add the function to the parser context
        std::cout << "Adding custom function 'is_red' to parser context..." << std::endl;
        parser.add_decl(is_red);
        
        // Now we can parse SMTLIB2 strings that use these custom symbols
        std::cout << "\nParsing with custom symbols..." << std::endl;
        ast_vector formulas(ctx, parser.parse_string(
            "(declare-const c1 Color)\n"
            "(declare-const c2 Color)\n"
            "(assert (is_red c1))\n"
            "(assert (not (is_red c2)))"));
        
        std::cout << "Parsed " << formulas.size() << " formulas:" << std::endl;
        for (unsigned i = 0; i < formulas.size(); i++) {
            std::cout << "  " << Z3_ast_to_string(ctx, formulas.get(i)) << std::endl;
        }
    } // parser and formulas destructors run here, before Z3_del_context
    
    Z3_del_context(ctx);
}

/**
   \brief Example demonstrating a practical use case: building an interactive theorem prover.
   
   This shows how parser_context can maintain state across multiple user interactions.
*/
void parser_context_interactive_example() {
    std::cout << "\n=== Interactive Session Example ===" << std::endl;
    
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    {
        parser_context parser(ctx);
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        
        // Simulate an interactive session with multiple commands
        std::cout << "Session command 1: Define the problem domain..." << std::endl;
        {
            ast_vector formulas(ctx, parser.parse_string(
                "(declare-const a Int)\n"
                "(declare-const b Int)\n"
                "(declare-const c Int)"));
            for (unsigned i = 0; i < formulas.size(); i++) {
                Z3_solver_assert(ctx, solver, formulas.get(i));
            }
        }
        
        std::cout << "Session command 2: Add first constraint..." << std::endl;
        {
            ast_vector formulas(ctx, parser.parse_string(
                "(assert (= (+ a b) c))"));
            for (unsigned i = 0; i < formulas.size(); i++) {
                Z3_solver_assert(ctx, solver, formulas.get(i));
            }
        }
        
        std::cout << "Session command 3: Add more constraints..." << std::endl;
        {
            ast_vector formulas(ctx, parser.parse_string(
                "(assert (> a 0))\n"
                "(assert (> b 0))\n"
                "(assert (= c 10))"));
            for (unsigned i = 0; i < formulas.size(); i++) {
                Z3_solver_assert(ctx, solver, formulas.get(i));
            }
        }
        
        std::cout << "\nSession command 4: Check satisfiability..." << std::endl;
        Z3_lbool result = Z3_solver_check(ctx, solver);
        if (result == Z3_L_TRUE) {
            std::cout << "SAT - Found a solution!" << std::endl;
            Z3_model model = Z3_solver_get_model(ctx, solver);
            Z3_model_inc_ref(ctx, model);
            std::cout << "Model:\n" << Z3_model_to_string(ctx, model) << std::endl;
            Z3_model_dec_ref(ctx, model);
        } else if (result == Z3_L_FALSE) {
            std::cout << "UNSAT - No solution exists" << std::endl;
        } else {
            std::cout << "UNKNOWN" << std::endl;
        }
        
        // Cleanup
        Z3_solver_dec_ref(ctx, solver);
    } // parser destructors run here
    
    Z3_del_context(ctx);
}

/**
   \brief Main function demonstrating all parser context examples.
*/
int main() {
    std::cout << "Z3 Parser Context Examples" << std::endl;
    std::cout << "==========================" << std::endl;
    std::cout << "\nThese examples demonstrate the Z3_parser_context API," << std::endl;
    std::cout << "which allows incremental parsing of SMTLIB2 commands." << std::endl;
    
    parser_context_basic_example();
    parser_context_custom_decls_example();
    parser_context_interactive_example();
    
    std::cout << "\n=== All examples completed successfully ===" << std::endl;
    
    return 0;
}
