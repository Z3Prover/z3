/*++
Copyright (c) 2026 Microsoft Corporation

Test file for move semantics of z3::context
--*/

#include <iostream>
#include <utility>
#include <cassert>
#include "z3++.h"

using namespace z3;

// Test move constructor
void test_move_constructor() {
    std::cout << "Testing move constructor...\n";
    
    context c1;
    
    // Move construct c2 from c1
    context c2(std::move(c1));
    
    // c2 should now own the context, and we can use it
    expr x = c2.int_const("x");
    solver s(c2);
    s.add(x > 0);
    
    check_result result = s.check();
    assert(result == sat);
    
    std::cout << "Move constructor test passed!\n";
}

// Test move assignment operator
void test_move_assignment() {
    std::cout << "Testing move assignment operator...\n";
    
    context c1;
    
    context c2;
    
    // Move assign c1 to c2
    c2 = std::move(c1);
    
    // c2 should now own c1's context, and we can use it
    expr x = c2.int_const("x");
    solver s(c2);
    s.add(x > 0);
    
    check_result result = s.check();
    assert(result == sat);
    
    std::cout << "Move assignment test passed!\n";
}

// Test moving context into a function
context create_context_with_config() {
    context c;
    c.set("timeout", 5000);
    return c; // Will use move constructor
}

void test_return_by_value() {
    std::cout << "Testing return by value...\n";
    
    context c = create_context_with_config();
    
    // Use the returned context
    expr x = c.int_const("x");
    solver s(c);
    s.add(x > 0);
    
    check_result result = s.check();
    assert(result == sat);
    
    std::cout << "Return by value test passed!\n";
}

// Test storing context in a container (e.g., vector)
void test_vector_storage() {
    std::cout << "Testing vector storage...\n";
    
    std::vector<context> contexts;
    
    // Create a context and move it into the vector
    context c;
    contexts.push_back(std::move(c));
    
    // Use the context from the vector
    expr x = contexts[0].int_const("x");
    solver s(contexts[0]);
    s.add(x > 0);
    
    check_result result = s.check();
    assert(result == sat);
    
    std::cout << "Vector storage test passed!\n";
}

int main() {
    std::cout << "Running z3::context move semantics tests...\n\n";
    
    try {
        test_move_constructor();
        test_move_assignment();
        test_return_by_value();
        test_vector_storage();
        
        std::cout << "\nAll tests passed!\n";
        return 0;
    }
    catch (const exception& e) {
        std::cerr << "Test failed with exception: " << e << "\n";
        return 1;
    }
}
