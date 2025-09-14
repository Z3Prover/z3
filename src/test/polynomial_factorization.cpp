/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    polynomial_factorization.cpp

Abstract:

    Tests for polynomial factorization functionality in math/polynomial

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "math/polynomial/upolynomial.h"
#include "math/polynomial/upolynomial_factorization.h"
#include "util/rlimit.h"
#include <iostream>

namespace polynomial {

void test_factorization_basic() {
    std::cout << "test_factorization_basic\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(m);
    
    // Test factorization of x^2 - 1 = (x-1)(x+1)
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^2 - 1: coefficients [c_0, c_1, c_2] = [-1, 0, 1]
    p.push_back(mpz(-1));  // constant term
    p.push_back(mpz(0));   // x coefficient  
    p.push_back(mpz(1));   // x^2 coefficient
    
    m.factor(p, fs);
    
    // Should have 2 distinct factors: (x-1) and (x+1)
    VERIFY(fs.distinct_factors() == 2);
    
    // Reconstruct polynomial from factors
    upolynomial::scoped_numeral_vector result(m);
    fs.multiply(result);
    
    VERIFY(m.eq(p, result));
}

void test_factorization_irreducible() {
    std::cout << "test_factorization_irreducible\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(m);
    
    // Test irreducible polynomial x^2 + 1 (over rationals)
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^2 + 1: coefficients [1, 0, 1]
    p.push_back(mpz(1));   // constant term
    p.push_back(mpz(0));   // x coefficient
    p.push_back(mpz(1));   // x^2 coefficient
    
    m.factor(p, fs);
    
    // Should have 1 distinct factor (irreducible)
    VERIFY(fs.distinct_factors() == 1);
    
    // Reconstruct polynomial from factors
    upolynomial::scoped_numeral_vector result(m);
    fs.multiply(result);
    
    VERIFY(m.eq(p, result));
}

void test_factorization_cubic() {
    std::cout << "test_factorization_cubic\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(m);
    
    // Test factorization of x^3 - 6x^2 + 11x - 6 = (x-1)(x-2)(x-3)
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^3 - 6x^2 + 11x - 6: coefficients [-6, 11, -6, 1]
    p.push_back(mpz(-6));  // constant term
    p.push_back(mpz(11));  // x coefficient
    p.push_back(mpz(-6));  // x^2 coefficient
    p.push_back(mpz(1));   // x^3 coefficient
    
    m.factor(p, fs);
    
    // Should have 3 distinct factors: (x-1), (x-2), (x-3)
    VERIFY(fs.distinct_factors() == 3);
    
    // Reconstruct polynomial from factors
    upolynomial::scoped_numeral_vector result(m);
    fs.multiply(result);
    
    VERIFY(m.eq(p, result));
}

void test_factorization_repeated_factors() {
    std::cout << "test_factorization_repeated_factors\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(m);
    
    // Test factorization of (x-1)^3 = x^3 - 3x^2 + 3x - 1
    upolynomial::scoped_numeral_vector p(m);
    
    // Create polynomial x^3 - 3x^2 + 3x - 1: coefficients [-1, 3, -3, 1]
    p.push_back(mpz(-1));  // constant term
    p.push_back(mpz(3));   // x coefficient
    p.push_back(mpz(-3));  // x^2 coefficient
    p.push_back(mpz(1));   // x^3 coefficient
    
    m.factor(p, fs);
    
    // Should have 1 distinct factor with multiplicity 3
    VERIFY(fs.distinct_factors() == 1);
    
    // Check that factor has degree 3 (meaning (x-1)^3)
    unsigned total_degree = 0;
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        total_degree += m.degree(fs[i]) * fs.get_degree(i);
    }
    VERIFY(total_degree == 3);
}

void test_factorization_constant() {
    std::cout << "test_factorization_constant\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(m);
    
    // Test constant polynomial 5
    upolynomial::scoped_numeral_vector p(m);
    p.push_back(mpz(5));  // constant term
    
    m.factor(p, fs);
    
    // Should have 0 distinct factors (constant)
    VERIFY(fs.distinct_factors() == 0);
    
    // The constant should be 5
    VERIFY(nm.eq(fs.get_constant(), mpz(5)));
}

void test_factorization_zero() {
    std::cout << "test_factorization_zero\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    upolynomial::factors fs(m);
    
    // Test zero polynomial
    upolynomial::scoped_numeral_vector p(m);
    p.push_back(mpz(0));  // just zero
    
    m.factor(p, fs);
    
    // Zero polynomial should have 0 factors or be detected as zero
    VERIFY(fs.distinct_factors() == 0 || m.is_zero(const_cast<upolynomial::numeral_vector&>(fs[0])));
}

void test_factorization_gcd() {
    std::cout << "test_factorization_gcd\n";
    
    reslimit rl;
    unsynch_mpq_manager nm;
    upolynomial::manager m(rl, nm);
    
    // Test GCD computation with polynomials
    upolynomial::scoped_numeral_vector p1(m), p2(m), gcd_result(m);
    
    // p1 = x^2 - 1 = (x-1)(x+1)
    p1.push_back(mpz(-1)); // constant
    p1.push_back(mpz(0));  // x
    p1.push_back(mpz(1));  // x^2
    
    // p2 = x^3 - 1 = (x-1)(x^2+x+1) 
    p2.push_back(mpz(-1)); // constant
    p2.push_back(mpz(0));  // x
    p2.push_back(mpz(0));  // x^2  
    p2.push_back(mpz(1));  // x^3
    
    m.gcd(p1, p2, gcd_result);
    
    // GCD should be (x-1), which is [-1, 1] in coefficient form
    VERIFY(m.degree(gcd_result) == 1);
    VERIFY(nm.eq(gcd_result[0], mpz(-1)));
    VERIFY(nm.eq(gcd_result[1], mpz(1)));
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