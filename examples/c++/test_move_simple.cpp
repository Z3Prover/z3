/*++
Copyright (c) 2026 Microsoft Corporation

Simple test file for move semantics of z3::context
--*/

#include <iostream>
#include <utility>
#include "z3++.h"

using namespace z3;

int main() {
    std::cout << "Test 1: Move constructor\n";
    {
        context c1;
        std::cout << "Created c1\n";
        
        context c2(std::move(c1));
        std::cout << "Moved c1 to c2\n";
        
        expr x = c2.int_const("x");
        std::cout << "Created expression in c2\n";
    }
    std::cout << "Test 1 passed!\n\n";
    
    std::cout << "Test 2: Move assignment\n";
    {
        context c1;
        std::cout << "Created c1\n";
        
        context c2;
        std::cout << "Created c2\n";
        
        c2 = std::move(c1);
        std::cout << "Move assigned c1 to c2\n";
        
        expr x = c2.int_const("x");
        std::cout << "Created expression in c2\n";
    }
    std::cout << "Test 2 passed!\n\n";
    
    std::cout << "All tests passed!\n";
    return 0;
}
