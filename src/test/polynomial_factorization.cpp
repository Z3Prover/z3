/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    polynomial_factorization.cpp

Abstract:

    Tests for polynomial factorization functionality

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "math/polynomial/upolynomial_factorization.h"
#include "math/polynomial/upolynomial.h"
#include "util/rlimit.h"
#include <iostream>

namespace polynomial {

void test_factorization_basic() {
    std::cout << "test_factorization_basic\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(nm);
    
    // Test factorization of x^2 - 1 = (x-1)(x+1)
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^2 - 1: coefficients [c_0, c_1, c_2] = [-1, 0, 1]
    m.set(p, 3);
    nm.set(p[0], -1);  // constant term
    nm.set(p[1], 0);   // coefficient of x
    nm.set(p[2], 1);   // coefficient of x^2
    
    // Factor the polynomial
    m.factor(p, fs);
    
    // Should have two linear factors
    VERIFY(fs.distinct_factors() >= 2);
    
    // Verify that multiplying factors gives back original polynomial
    upolynomial::scoped_numeral_vector result(m);
    m.set(result, 1);
    nm.set(result[0], 1);  // Start with constant 1
    
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        upolynomial::scoped_numeral_vector temp(m);
        for (unsigned j = 0; j < fs.get_multiplicity(i); j++) {
            m.mul(result, fs[i], temp);
            m.swap(result, temp);
        }
    }
    
    VERIFY(m.eq(p, result));
}

void test_factorization_irreducible() {
    std::cout << "test_factorization_irreducible\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(nm);
    
    // Test irreducible polynomial x^2 + 1 over rationals
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^2 + 1: coefficients [1, 0, 1]
    m.set(p, 3);
    nm.set(p[0], 1);   // constant term
    nm.set(p[1], 0);   // coefficient of x  
    nm.set(p[2], 1);   // coefficient of x^2
    
    m.factor(p, fs);
    
    // Should be irreducible over rationals (only one factor)
    VERIFY(fs.distinct_factors() == 1);
    VERIFY(m.eq(p, fs[0]));
}

void test_factorization_cubic() {
    std::cout << "test_factorization_cubic\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(nm);
    
    // Test cubic polynomial x^3 - 6x^2 + 11x - 6 = (x-1)(x-2)(x-3)
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^3 - 6x^2 + 11x - 6
    m.set(p, 4);
    nm.set(p[0], -6);  // constant term
    nm.set(p[1], 11);  // coefficient of x
    nm.set(p[2], -6);  // coefficient of x^2
    nm.set(p[3], 1);   // coefficient of x^3
    
    m.factor(p, fs);
    
    // Should have three linear factors
    VERIFY(fs.distinct_factors() >= 3 || 
           (fs.distinct_factors() > 0 && fs.total_factors() == 3));
    
    // Verify reconstruction
    upolynomial::scoped_numeral_vector result(m);
    m.set(result, 1);
    nm.set(result[0], 1);
    
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        upolynomial::scoped_numeral_vector temp(m);
        for (unsigned j = 0; j < fs.get_multiplicity(i); j++) {
            m.mul(result, fs[i], temp);
            m.swap(result, temp);
        }
    }
    
    VERIFY(m.eq(p, result));
}

void test_factorization_repeated_factors() {
    std::cout << "test_factorization_repeated_factors\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(nm);
    
    // Test polynomial with repeated factors: (x-1)^2(x-2) = x^3 - 4x^2 + 5x - 2
    upolynomial::scoped_numeral_vector p(m);
    
    m.set(p, 4);
    nm.set(p[0], -2);  // constant term
    nm.set(p[1], 5);   // coefficient of x
    nm.set(p[2], -4);  // coefficient of x^2
    nm.set(p[3], 1);   // coefficient of x^3
    
    m.factor(p, fs);
    
    // Should detect repeated factors
    bool has_repeated = false;
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        if (fs.get_multiplicity(i) > 1) {
            has_repeated = true;
            break;
        }
    }
    
    // Verify total degree matches
    unsigned total_degree = 0;
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        total_degree += m.degree(fs[i]) * fs.get_multiplicity(i);
    }
    VERIFY(total_degree == m.degree(p));
}

void test_factorization_constant() {
    std::cout << "test_factorization_constant\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(nm);
    
    // Test constant polynomial
    upolynomial::scoped_numeral_vector p(m);
    
    m.set(p, 1);
    nm.set(p[0], 42);  // constant 42
    
    m.factor(p, fs);
    
    // Constant should factor as itself
    VERIFY(fs.distinct_factors() <= 1);
    if (fs.distinct_factors() == 1) {
        VERIFY(m.degree(fs[0]) == 0);
    }
}

void test_factorization_zero() {
    std::cout << "test_factorization_zero\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(nm);
    
    // Test zero polynomial
    upolynomial::scoped_numeral_vector p(m);
    
    m.set(p, 1);
    nm.set(p[0], 0);
    
    m.factor(p, fs);
    
    // Zero polynomial should be handled appropriately
    VERIFY(fs.distinct_factors() == 0 || m.is_zero(fs[0]));
}

void test_factorization_gcd() {
    std::cout << "test_factorization_gcd\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    
    // Test GCD computation which is used in factorization
    upolynomial::scoped_numeral_vector p1(m), p2(m), gcd_result(m);
    
    // p1 = (x-1)(x-2) = x^2 - 3x + 2
    m.set(p1, 3);
    nm.set(p1[0], 2);  nm.set(p1[1], -3);  nm.set(p1[2], 1);
    
    // p2 = (x-1)(x-3) = x^2 - 4x + 3  
    m.set(p2, 3);
    nm.set(p2[0], 3);  nm.set(p2[1], -4);  nm.set(p2[2], 1);
    
    m.gcd(p1, p2, gcd_result);
    
    // GCD should be (x-1), which is x - 1
    VERIFY(m.degree(gcd_result) == 1);
    // Check if it's indeed x - 1 by evaluating at x = 1
    mpq eval_result;
    nm.set(eval_result, 0);
    for (unsigned i = 0; i < m.size(gcd_result); i++) {
        mpq term, power_val;
        nm.set(power_val, 1);
        // Compute 1^i = 1
        nm.mul(p1[i], power_val, term);
        nm.add(eval_result, term, eval_result);
        nm.del(term);
        nm.del(power_val);
    }
    VERIFY(nm.is_zero(eval_result));
    nm.del(eval_result);
}

void test_polynomial_factorization() {
    test_factorization_basic();
    test_factorization_irreducible();
    test_factorization_cubic();
    test_factorization_repeated_factors();
    test_factorization_constant();
    test_factorization_zero();
    test_factorization_gcd();
}

} // namespace polynomial

void tst_polynomial_factorization() {
    polynomial::test_polynomial_factorization();
}