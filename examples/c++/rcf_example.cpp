/**
   \brief Example demonstrating the RCF (Real Closed Field) API in C++.
   
   This example shows how to use RCF numerals to work with:
   - Transcendental numbers (pi, e)
   - Algebraic numbers (roots of polynomials)
   - Infinitesimals
   - Exact real arithmetic
*/
#include <iostream>
#include "z3++.h"

using namespace z3;

void rcf_basic_example() {
    std::cout << "RCF Basic Example\n";
    std::cout << "=================\n";
    
    context c;
    
    // Create pi and e
    rcf_num pi = rcf_pi(c);
    rcf_num e = rcf_e(c);
    
    std::cout << "pi = " << pi << "\n";
    std::cout << "e = " << e << "\n";
    
    // Arithmetic operations
    rcf_num sum = pi + e;
    rcf_num prod = pi * e;
    
    std::cout << "pi + e = " << sum << "\n";
    std::cout << "pi * e = " << prod << "\n";
    
    // Decimal approximations
    std::cout << "pi (10 decimals) = " << pi.to_decimal(10) << "\n";
    std::cout << "e (10 decimals) = " << e.to_decimal(10) << "\n";
    
    // Comparisons
    std::cout << "pi < e? " << (pi < e ? "yes" : "no") << "\n";
    std::cout << "pi > e? " << (pi > e ? "yes" : "no") << "\n";
}

void rcf_rational_example() {
    std::cout << "\nRCF Rational Example\n";
    std::cout << "====================\n";
    
    context c;
    
    // Create rational numbers
    rcf_num half(c, "1/2");
    rcf_num third(c, "1/3");
    
    std::cout << "1/2 = " << half << "\n";
    std::cout << "1/3 = " << third << "\n";
    
    // Arithmetic
    rcf_num sum = half + third;
    std::cout << "1/2 + 1/3 = " << sum << "\n";
    
    // Type queries
    std::cout << "Is 1/2 rational? " << (half.is_rational() ? "yes" : "no") << "\n";
    std::cout << "Is 1/2 algebraic? " << (half.is_algebraic() ? "yes" : "no") << "\n";
}

void rcf_roots_example() {
    std::cout << "\nRCF Roots Example\n";
    std::cout << "=================\n";
    
    context c;
    
    // Find roots of x^2 - 2 = 0
    // Polynomial: -2 + 0*x + 1*x^2
    std::vector<rcf_num> coeffs;
    coeffs.push_back(rcf_num(c, -2));   // constant term
    coeffs.push_back(rcf_num(c, 0));    // x coefficient
    coeffs.push_back(rcf_num(c, 1));    // x^2 coefficient
    
    std::vector<rcf_num> roots = rcf_roots(c, coeffs);
    
    std::cout << "Roots of x^2 - 2 = 0:\n";
    for (size_t i = 0; i < roots.size(); i++) {
        std::cout << "  root[" << i << "] = " << roots[i] << "\n";
        std::cout << "  decimal = " << roots[i].to_decimal(15) << "\n";
        std::cout << "  is_algebraic = " << (roots[i].is_algebraic() ? "yes" : "no") << "\n";
    }
}

void rcf_infinitesimal_example() {
    std::cout << "\nRCF Infinitesimal Example\n";
    std::cout << "=========================\n";
    
    context c;
    
    // Create an infinitesimal
    rcf_num eps = rcf_infinitesimal(c);
    std::cout << "eps = " << eps << "\n";
    std::cout << "Is eps infinitesimal? " << (eps.is_infinitesimal() ? "yes" : "no") << "\n";
    
    // Infinitesimals are smaller than any positive real number
    rcf_num tiny(c, "1/1000000000");
    std::cout << "eps < 1/1000000000? " << (eps < tiny ? "yes" : "no") << "\n";
}

int main() {
    try {
        rcf_basic_example();
        rcf_rational_example();
        rcf_roots_example();
        rcf_infinitesimal_example();
        
        std::cout << "\nAll RCF examples completed successfully!\n";
        return 0;
    }
    catch (exception& e) {
        std::cerr << "Z3 exception: " << e << "\n";
        return 1;
    }
}
