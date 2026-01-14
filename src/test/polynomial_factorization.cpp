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
    for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
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

void test_factorization_large_multivariate_missing_factors() {
    std::cout << "test_factorization_large_multivariate_missing_factors\n";

    reslimit rl;
    numeral_manager nm;
    manager m(rl, nm);

    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());

    struct term_t {
        int coeff;
        unsigned e0;
        unsigned e1;
        unsigned e2;
    };

    /*
    - x2^8 - x1 x2^7 - x0 x2^7 + 48 x2^7 + 2 x1^2 x2^6 + x0 x1 x2^6 + 132 x1 x2^6 + 2 x0^2 x2^6 + 132 x0 x2^6 
    - 144 x2^6 + 2 x1^3 x2^5 + 6 x0 x1^2 x2^5 + 180 x1^2 x2^5 + 6 x0^2 x1 x2^5 + 432 x0 x1 x2^5 - 
    864 x1 x2^5 + 2 x0^3 x2^5 + 180 x0^2 x2^5 - 864 x0 x2^5 - x1^4 x2^4 + 2 x0 x1^3 x2^4 + 
    156 x1^3 x2^4 + 3 x0^2 x1^2 x2^4 + 684 x0 x1^2 x2^4 - 1620 x1^2 x2^4 + 2 x0^3 x1 x2^4 + 684 x0^2 x1 x2^4 - 
    4536 x0 x1 x2^4 - x0^4 x2^4 + 156 x0^3 x2^4 - 1620 x0^2 x2^4 - x1^5 x2^3 - 5 x0 x1^4 x2^3 + 60 x1^4 x2^3 - 
    7 x0^2 x1^3 x2^3 + 600 x0 x1^3 x2^3 - 900 x1^3 x2^3 - 7 x0^3 x1^2 x2^3 + 1080 x0^2 x1^2 x2^3 - 7452 x0 x1^2 x2^3 - 
    5 x0^4 x1 x2^3 + 600 x0^3 x1 x2^3 - 7452 x0^2 x1 x2^3 - x0^5 x2^3 + 60 x0^4 x2^3 - 900 x0^3 x2^3 - 3 x0 x1^5 x2^2 -
     9 x0^2 x1^4 x2^2 + 216 x0 x1^4 x2^2 - 13 x0^3 x1^3 x2^2 + 828 x0^2 x1^3 x2^2 - 3780 x0 x1^3 x2^2 - 9 x0^4 x1^2 x2^2 + 
     828 x0^3 x1^2 x2^2 - 11016 x0^2 x1^2 x2^2 - 3 x0^5 x1 x2^2 + 216 x0^4 x1 x2^2 - 3780 x0^3 x1 x2^2 - 3 x0^2 x1^5 x2 - 
     7 x0^3 x1^4 x2 + 252 x0^2 x1^4 x2 - 7 x0^4 x1^3 x2 + 480 x0^3 x1^3 x2 - 5184 x0^2 x1^3 x2 - 3 x0^5 x1^2 x2 + 
     252 x0^4 x1^2 x2 - 5184 x0^3 x1^2 x2 - x0^3 x1^5 - 2 x0^4 x1^4 + 96 x0^3 x1^4 - x0^5 x1^3 + 96 x0^4 x1^3 - 2304 x0^3 x1^3
     */ 
    static const term_t terms[] = {
        { -1, 0u, 0u, 8u },
        { -1, 0u, 1u, 7u },
        { -1, 1u, 0u, 7u },
        { 48, 0u, 0u, 7u },
        { 2, 0u, 2u, 6u },
        { 1, 1u, 1u, 6u },
        { 132, 0u, 1u, 6u },
        { 2, 2u, 0u, 6u },
        { 132, 1u, 0u, 6u },
        { -144, 0u, 0u, 6u },
        { 2, 0u, 3u, 5u },
        { 6, 1u, 2u, 5u },
        { 180, 0u, 2u, 5u },
        { 6, 2u, 1u, 5u },
        { 432, 1u, 1u, 5u },
        { -864, 0u, 1u, 5u },
        { 2, 3u, 0u, 5u },
        { 180, 2u, 0u, 5u },
        { -864, 1u, 0u, 5u },
        { -1, 0u, 4u, 4u },
        { 2, 1u, 3u, 4u },
        { 156, 0u, 3u, 4u },
        { 3, 2u, 2u, 4u },
        { 684, 1u, 2u, 4u },
        { -1620, 0u, 2u, 4u },
        { 2, 3u, 1u, 4u },
        { 684, 2u, 1u, 4u },
        { -4536, 1u, 1u, 4u },
        { -1, 4u, 0u, 4u },
        { 156, 3u, 0u, 4u },
        { -1620, 2u, 0u, 4u },
        { -1, 0u, 5u, 3u },
        { -5, 1u, 4u, 3u },
        { 60, 0u, 4u, 3u },
        { -7, 2u, 3u, 3u },
        { 600, 1u, 3u, 3u },
        { -900, 0u, 3u, 3u },
        { -7, 3u, 2u, 3u },
        { 1080, 2u, 2u, 3u },
        { -7452, 1u, 2u, 3u },
        { -5, 4u, 1u, 3u },
        { 600, 3u, 1u, 3u },
        { -7452, 2u, 1u, 3u },
        { -1, 5u, 0u, 3u },
        { 60, 4u, 0u, 3u },
        { -900, 3u, 0u, 3u },
        { -3, 1u, 5u, 2u },
        { -9, 2u, 4u, 2u },
        { 216, 1u, 4u, 2u },
        { -13, 3u, 3u, 2u },
        { 828, 2u, 3u, 2u },
        { -3780, 1u, 3u, 2u },
        { -9, 4u, 2u, 2u },
        { 828, 3u, 2u, 2u },
        { -11016, 2u, 2u, 2u },
        { -3, 5u, 1u, 2u },
        { 216, 4u, 1u, 2u },
        { -3780, 3u, 1u, 2u },
        { -3, 2u, 5u, 1u },
        { -7, 3u, 4u, 1u },
        { 252, 2u, 4u, 1u },
        { -7, 4u, 3u, 1u },
        { 480, 3u, 3u, 1u },
        { -5184, 2u, 3u, 1u },
        { -3, 5u, 2u, 1u },
        { 252, 4u, 2u, 1u },
        { -5184, 3u, 2u, 1u },
        { -1, 3u, 5u, 0u },
        { -2, 4u, 4u, 0u },
        { 96, 3u, 4u, 0u },
        { -1, 5u, 3u, 0u },
        { 96, 4u, 3u, 0u },
        { -2304, 3u, 3u, 0u },
    };

    polynomial_ref p(m);
    p = m.mk_zero();

    for (const auto & term : terms) {
        polynomial_ref t(m);
        t = m.mk_const(rational(term.coeff));
        if (term.e0 != 0) {
            t = t * (x0 ^ term.e0);
        }
        if (term.e1 != 0) {
            t = t * (x1 ^ term.e1);
        }
        if (term.e2 != 0) {
            t = t * (x2 ^ term.e2);
        }
        p = p + t;
    }

    factors fs(m);
    factor(p, fs);
    VERIFY(fs.distinct_factors() == 2); // indeed there are 3 factors, that is demonstrated by the loop  
    for (unsigned i = 0; i < fs.distinct_factors(); ++i) {
        polynomial_ref f(m);
        f = fs[i];
        if (degree(f, x1)<= 1) continue;
        factors fs0(m);
        factor(f, fs0);
        VERIFY(fs0.distinct_factors() >= 2);
    }

    polynomial_ref reconstructed(m);
    fs.multiply(reconstructed);
    VERIFY(eq(reconstructed, p));
}

void test_factorization_multivariate_missing_factors() {
    std::cout << "test_factorization_multivariate_missing_factors\n";

    reslimit rl;
    numeral_manager nm;
    manager m(rl, nm);

    polynomial_ref x0(m);
    polynomial_ref x1(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());

    polynomial_ref p(m);
    p = (x0 + x1) * (x0 + (2 * x1)) * (x0 + (3 * x1));

    factors fs(m);
    factor(p, fs);

    // Multivariate factorization stops after returning the whole polynomial.
    VERIFY(fs.distinct_factors() == 1);
    VERIFY(m.degree(fs[0], 0) == 3);

    factors fs_refined(m);
    polynomial_ref residual = fs[0];
    factor(residual, fs_refined);

    // A second attempt still fails to expose the linear factors.
    VERIFY(fs_refined.distinct_factors() == 1); // actually we need 3 factors
    VERIFY(m.degree(fs_refined[0], 0) == 3); // actually we need degree 1

    polynomial_ref reconstructed(m);
    fs.multiply(reconstructed);
    VERIFY(eq(reconstructed, p));
}

void test_polynomial_factorization() {
    test_factorization_large_multivariate_missing_factors();
    test_factorization_multivariate_missing_factors();
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
