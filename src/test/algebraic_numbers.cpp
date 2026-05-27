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
    anum_manager am(rl, qm);
    
    // Test basic algebraic number creation and operations
    scoped_anum a(am), b(am), c(am);
    
    // Set a = 2, b = 3
    scoped_mpq q2(qm), q3(qm);
    qm.set(q2, 2);
    qm.set(q3, 3);
    am.set(a, q2);
    am.set(b, q3);
    
    // Test addition: c = a + b = 2 + 3 = 5
    am.add(a, b, c);
    
    scoped_mpq q5(qm);
    qm.set(q5, 5);
    VERIFY(am.eq(c, q5));
}

void test_algebraic_arithmetic() {
    std::cout << "test_algebraic_arithmetic\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    anum_manager am(rl, qm);
    
    scoped_anum a(am), b(am), sum(am), diff(am), prod(am);
    
    // Set a = 5/2, b = 3/4
    scoped_mpq qa(qm), qb(qm);
    qm.set(qa, 5, 2);
    qm.set(qb, 3, 4);
    am.set(a, qa);
    am.set(b, qb);
    
    // Test arithmetic operations
    am.add(a, b, sum);     // 5/2 + 3/4 = 13/4
    am.sub(a, b, diff);    // 5/2 - 3/4 = 7/4
    am.mul(a, b, prod);    // 5/2 * 3/4 = 15/8
    
    // Verify results
    scoped_mpq qsum(qm), qdiff(qm), qprod(qm);
    qm.set(qsum, 13, 4);
    qm.set(qdiff, 7, 4);
    qm.set(qprod, 15, 8);
    
    VERIFY(am.eq(sum, qsum));
    VERIFY(am.eq(diff, qdiff));
    VERIFY(am.eq(prod, qprod));
}

void test_algebraic_comparison() {
    std::cout << "test_algebraic_comparison\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    anum_manager am(rl, qm);
    
    scoped_anum a(am), b(am), c(am);
    
    // Set a = 2, b = 3, c = 2
    scoped_mpq q2(qm), q3(qm);
    qm.set(q2, 2);
    qm.set(q3, 3);
    am.set(a, q2);
    am.set(b, q3);
    am.set(c, q2);
    
    // Test comparisons
    VERIFY(am.lt(a, b));      // 2 < 3
    VERIFY(am.gt(b, a));      // 3 > 2
    VERIFY(am.eq(a, c));      // 2 == 2
    VERIFY(!am.eq(a, b));     // 2 != 3
}

void test_algebraic_comparison_edge_case() {
    std::cout << "test_algebraic_comparison edge case\n";

    // Let p1 = 1073741837 x^2 - 576460758745874510 x - 16106127555
    // Let p2 = p1 * (1073741837 x^2 - 576460759819616347 x -16106127555)
    //        = 1152921532524134569 x^4 - 1237940069261339757601884309 x^3
    //           + 332307006992839334837849081482577900 x^2 + 18569101038920096364028264635 x
    //           + 259407344817930278025
    // Compare a = root(p1, 1) in (-8, 0) and b = root(p2, 2) in (-15/2^29, -7/2^28)
    // The two numbers are different (a < b), but very close, and both are roots of p2
    
    reslimit rl;
    unsynch_mpq_manager qm;
    anum_manager am(rl, qm);
    manager m(rl, qm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());

    rational a0, a1, a2;
    a0 = 161061;
    a0 = (a0 * 100000) + 27555;
    a1 = 576460758;
    a1 = (a1 * 1000000000) + 745874510;
    a2 = 10737;
    a2 = (a2 * 100000) + 41837;

    rational b1;
    b1 = 576460759;
    b1 = (b1 * 1000000000) + 819616347;
    
    polynomial_ref p1(m);
    polynomial_ref p2(m);
    p1 = ((a2*x*x) - (a1*x)) - a0;
    p2 = p1 * (((a2*x*x) - (b1*x))  - a0);
    
    scoped_anum a(am), b(am);
    am.mk_root(p1, 1, a);
    am.mk_root(p2, 2, b);

    VERIFY(!am.eq(a, b));
}

void test_algebraic_degree() {
    std::cout << "test_algebraic_degree\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    anum_manager am(rl, qm);
    
    scoped_anum rational_num(am);
    
    // Test rational number
    scoped_mpq q(qm);
    qm.set(q, 5, 3);
    am.set(rational_num, q);
    
    // Rational numbers should be detected as rational
    VERIFY(am.is_rational(rational_num));
    
    // Test zero
    scoped_anum zero(am);
    am.reset(zero);
    VERIFY(am.is_zero(zero));
    VERIFY(am.is_rational(zero));
}

void test_algebraic_signs() {
    std::cout << "test_algebraic_signs\n";
    
    reslimit rl;
    unsynch_mpq_manager qm;
    anum_manager am(rl, qm);
    
    scoped_anum pos(am), neg(am), zero(am);
    
    // Set positive, negative, and zero values
    scoped_mpq qpos(qm), qneg(qm);
    qm.set(qpos, 5);
    qm.set(qneg, -3);
    am.set(pos, qpos);
    am.set(neg, qneg);
    am.reset(zero);
    
    // Test sign detection
    VERIFY(am.is_pos(pos));
    VERIFY(am.is_neg(neg));
    VERIFY(am.is_zero(zero));
    VERIFY(!am.is_pos(neg));
    VERIFY(!am.is_neg(pos));
    VERIFY(!am.is_zero(pos));
}

void test_algebraic_numbers() {
    test_algebraic_basic_operations();
    test_algebraic_arithmetic();
    test_algebraic_comparison();
    test_algebraic_comparison_edge_case();
    test_algebraic_degree();
    test_algebraic_signs();
}

} // namespace polynomial

void tst_algebraic_numbers() {
    polynomial::test_algebraic_numbers();
}