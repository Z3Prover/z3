/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    horner.cpp

Abstract:

    Tests for Horner evaluation functionality - simple polynomial evaluation

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "util/rational.h"
#include "util/vector.h"
#include <iostream>

// Simple horner evaluation function for testing
rational horner_eval(const vector<rational>& coeffs, const rational& x) {
    if (coeffs.empty()) return rational(0);
    
    rational result = coeffs.back();
    for (int i = coeffs.size() - 2; i >= 0; i--) {
        result = result * x + coeffs[i];
    }
    return result;
}

void test_horner_basic_evaluation() {
    std::cout << "test_horner_basic_evaluation\n";
    
    // Test basic polynomial evaluation using Horner's method
    // p(x) = 2x^3 + 3x^2 + 4x + 5
    vector<rational> coeffs;
    coeffs.push_back(rational(5));  // constant term
    coeffs.push_back(rational(4));  // coefficient of x
    coeffs.push_back(rational(3));  // coefficient of x^2
    coeffs.push_back(rational(2));  // coefficient of x^3
    
    rational x_val(2);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: 2*8 + 3*4 + 4*2 + 5 = 16 + 12 + 8 + 5 = 41
    VERIFY(result == rational(41));
}

void test_horner_linear_polynomial() {
    std::cout << "test_horner_linear_polynomial\n";
    
    // Test linear polynomial: p(x) = 3x + 7
    vector<rational> coeffs;
    coeffs.push_back(rational(7));  // constant term
    coeffs.push_back(rational(3));  // coefficient of x
    
    rational x_val(5);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: 3*5 + 7 = 22
    VERIFY(result == rational(22));
}

void test_horner_constant_polynomial() {
    std::cout << "test_horner_constant_polynomial\n";
    
    // Test constant polynomial: p(x) = 42
    vector<rational> coeffs;
    coeffs.push_back(rational(42));
    
    rational x_val(100);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: 42
    VERIFY(result == rational(42));
}

void test_horner_zero_polynomial() {
    std::cout << "test_horner_zero_polynomial\n";
    
    // Test zero polynomial: p(x) = 0
    vector<rational> coeffs;
    coeffs.push_back(rational(0));
    
    rational x_val(15);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: 0
    VERIFY(result == rational(0));
}

void test_horner_negative_coefficients() {
    std::cout << "test_horner_negative_coefficients\n";
    
    // Test polynomial with negative coefficients: p(x) = -2x^2 + 3x - 1
    vector<rational> coeffs;
    coeffs.push_back(rational(-1));  // constant term
    coeffs.push_back(rational(3));   // coefficient of x
    coeffs.push_back(rational(-2));  // coefficient of x^2
    
    rational x_val(2);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: -2*4 + 3*2 - 1 = -8 + 6 - 1 = -3
    VERIFY(result == rational(-3));
}

void test_horner_fractional_values() {
    std::cout << "test_horner_fractional_values\n";
    
    // Test with fractional coefficients and evaluation point
    // p(x) = (1/2)x^2 + (3/4)x + 1/3
    vector<rational> coeffs;
    coeffs.push_back(rational(1, 3));  // constant term
    coeffs.push_back(rational(3, 4));  // coefficient of x
    coeffs.push_back(rational(1, 2));  // coefficient of x^2
    
    rational x_val(2, 3);  // x = 2/3
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: (1/2)*(4/9) + (3/4)*(2/3) + 1/3 = 2/9 + 1/2 + 1/3
    // = 4/18 + 9/18 + 6/18 = 19/18
    VERIFY(result == rational(19, 18));
}

void test_horner_zero_evaluation_point() {
    std::cout << "test_horner_zero_evaluation_point\n";
    
    // Test evaluation at x = 0
    // p(x) = 5x^3 + 3x^2 + 2x + 7
    vector<rational> coeffs;
    coeffs.push_back(rational(7));  // constant term
    coeffs.push_back(rational(2));  // coefficient of x
    coeffs.push_back(rational(3));  // coefficient of x^2
    coeffs.push_back(rational(5));  // coefficient of x^3
    
    rational x_val(0);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: 7 (just the constant term)
    VERIFY(result == rational(7));
}

void test_horner_high_degree() {
    std::cout << "test_horner_high_degree\n";
    
    // Test higher degree polynomial: p(x) = x^5 + x^4 + x^3 + x^2 + x + 1
    vector<rational> coeffs;
    for (int i = 0; i <= 5; ++i) {
        coeffs.push_back(rational(1));
    }
    
    rational x_val(1);
    rational result = horner_eval(coeffs, x_val);
    
    // Expected: 1 + 1 + 1 + 1 + 1 + 1 = 6
    VERIFY(result == rational(6));
    
    // Test with x = -1
    x_val = rational(-1);
    result = horner_eval(coeffs, x_val);
    
    // Expected: (-1)^5 + (-1)^4 + (-1)^3 + (-1)^2 + (-1)^1 + 1 = -1 + 1 - 1 + 1 - 1 + 1 = 0
    VERIFY(result == rational(0));
}

void test_horner() {
    test_horner_basic_evaluation();
    test_horner_linear_polynomial();
    test_horner_constant_polynomial();
    test_horner_zero_polynomial();
    test_horner_negative_coefficients();
    test_horner_fractional_values();
    test_horner_zero_evaluation_point();
    test_horner_high_degree();
}

void tst_horner() {
    test_horner();
}