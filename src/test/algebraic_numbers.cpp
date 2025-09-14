/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    algebraic_numbers.cpp

Abstract:

    Tests for algebraic numbers functionality in math/polynomial

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "math/polynomial/algebraic_numbers.h"
#include "util/rlimit.h"
#include <iostream>

namespace polynomial {

void test_algebraic_basic_operations() {
    std::cout << "test_algebraic_basic_operations\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    pmanager pm(rl, qm);
    amanager am(rl, qm, pm);
    
    // Test basic algebraic number creation
    scoped_anum a(am), b(am), c(am);
    
    // Create algebraic number representing sqrt(2)
    polynomial_ref p(pm);
    var x = pm.mk_var();
    p = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(2));
    
    am.mk_root(a, p, 1);  // Positive root of x^2 - 2
    
    // Test that sqrt(2) squared equals 2
    am.mul(a, a, b);
    am.set(c, rational(2));
    
    VERIFY(am.eq(b, c));
}

void test_algebraic_arithmetic() {
    std::cout << "test_algebraic_arithmetic\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    pmanager pm(rl, qm);
    amanager am(rl, qm, pm);
    
    scoped_anum sqrt2(am), sqrt3(am), sum(am), expected(am);
    
    // Create sqrt(2) and sqrt(3)
    polynomial_ref p2(pm), p3(pm);
    var x = pm.mk_var();
    
    p2 = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(2));
    p3 = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(3));
    
    am.mk_root(sqrt2, p2, 1);
    am.mk_root(sqrt3, p3, 1);
    
    // Test addition: sqrt(2) + sqrt(3)
    am.add(sqrt2, sqrt3, sum);
    
    // Verify the sum is algebraic (should be a root of x^4 - 10x^2 + 1)
    polynomial_ref sum_poly(pm);
    sum_poly = pm.mk_polynomial(pm.mk_power(x, 4)) - 
               pm.mk_polynomial(pm.mk_mul(pm.mk_const(rational(10)), pm.mk_mul(x, x))) +
               pm.mk_const(rational(1));
    
    // Test that (sqrt(2) + sqrt(3))^4 - 10*(sqrt(2) + sqrt(3))^2 + 1 = 0
    scoped_anum sum_sq(am), sum_4th(am), ten_sum_sq(am), result(am);
    am.mul(sum, sum, sum_sq);
    am.mul(sum_sq, sum_sq, sum_4th);
    am.mul(sum_sq, rational(10), ten_sum_sq);
    
    am.sub(sum_4th, ten_sum_sq, result);
    am.add(result, rational(1), result);
    
    // The result should be close to zero (within algebraic precision)
    VERIFY(am.is_zero(result));
}

void test_algebraic_comparison() {
    std::cout << "test_algebraic_comparison\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    pmanager pm(rl, qm);
    amanager am(rl, qm, pm);
    
    scoped_anum sqrt2(am), sqrt3(am), rational_val(am);
    
    // Create sqrt(2) and sqrt(3)
    polynomial_ref p2(pm), p3(pm);
    var x = pm.mk_var();
    
    p2 = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(2));
    p3 = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(3));
    
    am.mk_root(sqrt2, p2, 1);
    am.mk_root(sqrt3, p3, 1);
    am.set(rational_val, rational(3, 2));
    
    // Test comparisons
    VERIFY(am.lt(sqrt2, sqrt3));  // sqrt(2) < sqrt(3)
    VERIFY(am.gt(sqrt2, rational_val));  // sqrt(2) > 1.5
    VERIFY(!am.eq(sqrt2, sqrt3));  // sqrt(2) != sqrt(3)
}

void test_algebraic_isolation() {
    std::cout << "test_algebraic_isolation\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    pmanager pm(rl, qm);
    amanager am(rl, qm, pm);
    
    // Test root isolation for polynomial with multiple roots
    polynomial_ref p(pm);
    var x = pm.mk_var();
    
    // Create polynomial (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
    p = pm.mk_polynomial(pm.mk_power(x, 3)) -
        pm.mk_polynomial(pm.mk_mul(pm.mk_const(rational(6)), pm.mk_mul(x, x))) +
        pm.mk_polynomial(pm.mk_mul(pm.mk_const(rational(11)), x)) -
        pm.mk_const(rational(6));
    
    scoped_anum root1(am), root2(am), root3(am);
    
    am.mk_root(root1, p, 0);  // First root (should be 1)
    am.mk_root(root2, p, 1);  // Second root (should be 2)
    am.mk_root(root3, p, 2);  // Third root (should be 3)
    
    VERIFY(am.eq(root1, rational(1)));
    VERIFY(am.eq(root2, rational(2)));
    VERIFY(am.eq(root3, rational(3)));
}

void test_algebraic_degree() {
    std::cout << "test_algebraic_degree\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    pmanager pm(rl, qm);
    amanager am(rl, qm, pm);
    
    scoped_anum rational_num(am), algebraic_num(am);
    
    // Test rational number (degree 1)
    am.set(rational_num, rational(5, 3));
    
    // Test algebraic number (degree 2 - sqrt(2))
    polynomial_ref p(pm);
    var x = pm.mk_var();
    p = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(2));
    am.mk_root(algebraic_num, p, 1);
    
    // Rational numbers should have minimal polynomials of degree 1
    VERIFY(am.is_rational(rational_num));
    
    // sqrt(2) should not be rational
    VERIFY(!am.is_rational(algebraic_num));
}

void test_algebraic_refinement() {
    std::cout << "test_algebraic_refinement\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    pmanager pm(rl, qm);
    amanager am(rl, qm, pm);
    
    // Test interval refinement for algebraic numbers
    scoped_anum sqrt2(am);
    polynomial_ref p(pm);
    var x = pm.mk_var();
    
    p = pm.mk_polynomial(pm.mk_mul(x, x)) - pm.mk_const(rational(2));
    am.mk_root(sqrt2, p, 1);
    
    // Get interval containing sqrt(2)
    scoped_anum lower(am), upper(am);
    am.get_lower(sqrt2, lower);
    am.get_upper(sqrt2, upper);
    
    // sqrt(2) should be between 1.4 and 1.5
    VERIFY(am.ge(sqrt2, rational(14, 10)));
    VERIFY(am.le(sqrt2, rational(15, 10)));
}

void test_algebraic_numbers() {
    test_algebraic_basic_operations();
    test_algebraic_arithmetic();
    test_algebraic_comparison();
    test_algebraic_isolation();
    test_algebraic_degree();
    test_algebraic_refinement();
}

} // namespace polynomial

void tst_algebraic_numbers() {
    polynomial::test_algebraic_numbers();
}