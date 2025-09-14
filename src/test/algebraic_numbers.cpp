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
    test_algebraic_degree();
    test_algebraic_signs();
}

} // namespace polynomial

void tst_algebraic_numbers() {
    polynomial::test_algebraic_numbers();
}