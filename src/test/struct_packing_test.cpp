/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    struct_packing_test.cpp

Abstract:

    Test to verify struct packing optimizations maintain expected sizes.

Author:

    GitHub Copilot 2024-01-30

--*/

#include "sat/sat_config.h"
#include "params/theory_bv_params.h"
#include <iostream>
#include <cstddef>

int main() {
    std::cout << "=== Struct Packing Optimization Tests ===\n\n";
    
    // Verify sat::config is optimally packed
    // Previous size was 408 bytes, optimized to 320 bytes
    std::cout << "sat::config size: " << sizeof(sat::config) << " bytes (expected: <= 320)\n";
    if (sizeof(sat::config) <= 320) {
        std::cout << "  PASS: sat::config size optimization maintained\n";
    } else {
        std::cout << "  FAIL: sat::config size regression detected!\n";
        return 1;
    }
    
    std::cout << "\n";
    
    // Verify theory_bv_params is optimally packed  
    // Previous size was 20 bytes, optimized to 16 bytes
    std::cout << "theory_bv_params size: " << sizeof(theory_bv_params) << " bytes (expected: <= 16)\n";
    if (sizeof(theory_bv_params) <= 16) {
        std::cout << "  PASS: theory_bv_params size optimization maintained\n";
    } else {
        std::cout << "  FAIL: theory_bv_params size regression detected!\n";
        return 1;
    }
    
    std::cout << "\n=== All tests passed ===\n";
    return 0;
}
