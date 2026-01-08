/*++
Copyright (c) 2024 Microsoft Corporation

Test program for missing C++ API functions added per GitHub discussion #8121
--*/

#include <iostream>
#include "z3++.h"

using namespace z3;

/**
 * Test congruence closure APIs
 */
void test_congruence_apis() {
    std::cout << "Test congruence APIs\n";
    
    context c;
    
    // Create uninterpreted sort and function
    sort A = c.uninterpreted_sort("A");
    func_decl f = function("f", A, A);
    
    // Create constants
    expr x = c.constant("x", A);
    expr y = c.constant("y", A);
    
    // Create a simple solver (required for congruence closure)
    solver s(c, solver::simple());
    
    // Add assertions: x = y
    s.add(x == y);
    
    // Check satisfiability
    check_result result = s.check();
    std::cout << "Check result: " << result << "\n";
    
    if (result == sat) {
        // Test congruence_root
        expr root_x = s.congruence_root(x);
        expr root_y = s.congruence_root(y);
        std::cout << "Root of x: " << root_x << "\n";
        std::cout << "Root of y: " << root_y << "\n";
        
        // Test congruence_next
        expr next_x = s.congruence_next(x);
        std::cout << "Next of x: " << next_x << "\n";
        
        // Test congruence_explain
        expr explanation = s.congruence_explain(x, y);
        std::cout << "Explanation for x == y: " << explanation << "\n";
    }
    
    std::cout << "Congruence APIs test completed\n\n";
}

/**
 * Test model sort universe APIs
 */
void test_model_sort_universe() {
    std::cout << "Test model sort universe APIs\n";
    
    context c;
    
    // Create uninterpreted sorts
    sort A = c.uninterpreted_sort("A");
    sort B = c.uninterpreted_sort("B");
    
    // Create constants of different sorts
    expr a1 = c.constant("a1", A);
    expr a2 = c.constant("a2", A);
    expr b1 = c.constant("b1", B);
    expr b2 = c.constant("b2", B);
    
    solver s(c);
    
    // Add constraints to make sorts non-trivial
    s.add(a1 != a2);
    s.add(b1 != b2);
    
    check_result result = s.check();
    std::cout << "Check result: " << result << "\n";
    
    if (result == sat) {
        model m = s.get_model();
        
        // Test num_sorts
        unsigned num = m.num_sorts();
        std::cout << "Number of sorts: " << num << "\n";
        
        // Test get_sort and sort_universe
        for (unsigned i = 0; i < num; i++) {
            sort si = m.get_sort(i);
            std::cout << "Sort " << i << ": " << si << "\n";
            
            // Get universe for this sort
            expr_vector universe = m.sort_universe(si);
            std::cout << "  Universe size: " << universe.size() << "\n";
            std::cout << "  Elements: ";
            for (unsigned j = 0; j < universe.size(); j++) {
                if (j > 0) std::cout << ", ";
                std::cout << universe[j];
            }
            std::cout << "\n";
        }
    }
    
    std::cout << "Model sort universe APIs test completed\n\n";
}

/**
 * Test that existing APIs still work (units, non_units, trail)
 */
void test_existing_apis() {
    std::cout << "Test existing APIs\n";
    
    context c;
    expr x = c.bool_const("x");
    expr y = c.bool_const("y");
    
    // Use simple solver for trail support
    solver s(c, solver::simple());
    s.add(x || y);
    
    check_result result = s.check();
    std::cout << "Check result: " << result << "\n";
    
    if (result == sat) {
        // Test units
        expr_vector units = s.units();
        std::cout << "Units: " << units.size() << " unit(s)\n";
        
        // Test non_units
        expr_vector non_units = s.non_units();
        std::cout << "Non-units: " << non_units.size() << " non-unit(s)\n";
        
        // Test trail (works with simple solver)
        expr_vector trail = s.trail();
        std::cout << "Trail: " << trail.size() << " decision(s)\n";
    }
    
    std::cout << "Existing APIs test completed\n\n";
}

int main() {
    try {
        std::cout << "=== Testing C++ API Missing Functions ===\n\n";
        
        test_congruence_apis();
        test_model_sort_universe();
        test_existing_apis();
        
        std::cout << "=== All tests passed! ===\n";
        return 0;
    }
    catch (const exception& e) {
        std::cerr << "Error: " << e.msg() << "\n";
        return 1;
    }
}
