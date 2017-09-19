/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    fixed_bit_vector.cpp

Abstract:

    Test fixed-size bit vector module

Author:

    Nikolaj Bjorner (nbjorner) 2014-9-15.

Revision History:

    based on bit_vector.cpp

--*/
#include<cstdlib>
#include<iostream>
#include "util/fixed_bit_vector.h"
#include "util/vector.h"


static void tst1() {
    fixed_bit_vector_manager m(30);
    fixed_bit_vector *b;
    b = m.allocate0();
    m.set(*b, 0, true);
    m.set(*b, 1, false);
    m.set(*b, 2, true);
    ENSURE(b->get(0) == true);
    ENSURE(b->get(1) == false);
    ENSURE(b->get(2) == true);
    ENSURE(b->get(3) == false);
    ENSURE(b->get(29) == false);
    m.deallocate(b);
}

static void tst_or() {
    {
        fixed_bit_vector_manager m(10);
        fixed_bit_vector *b1, *b2;
        b1 = m.allocate0();
        b2 = m.allocate0();

        m.set(*b1, 4);
        m.set(*b2, 8);
        m.set(*b2, 3);
        m.set(*b2, 2);
        m.set(*b2, 1);
        m.display(std::cout, *b1) << "\n";
        m.display(std::cout, *b2) << "\n";
        m.set_or(*b1, *b2);
        m.display(std::cout, *b1) << "\n";
        ENSURE(!m.equals(*b1, *b2));
        m.unset(*b1, 4);
        ENSURE(m.equals(*b1, *b2));
        m.unset(*b1, 3);
        ENSURE(!m.equals(*b1, *b2));
        m.deallocate(b1);
        m.deallocate(b2);
    }
}

static void tst_and() {

}



static void tst_eq(unsigned num_bits) {
    fixed_bit_vector_manager m(num_bits);
    fixed_bit_vector* b1 = m.allocate0();
    fixed_bit_vector* b2 = m.allocate0();
    fixed_bit_vector* b3 = m.allocate0();

    m.set(*b1, 3, true);
    ENSURE(!m.equals(*b1, *b2));
    ENSURE(m.equals(*b2, *b3));

    m.set(*b3, 3, true);
    ENSURE(m.equals(*b1, *b3));
    
    m.set(*b2, num_bits-1, true);
    m.set(*b3, num_bits-1);
    m.unset(*b3, 3);
    ENSURE(m.equals(*b2, *b3));
    m.fill0(*b1);
    m.set_neg(*b1);
    m.fill1(*b2);
    ENSURE(m.equals(*b1, *b2));
    m.fill0(*b1);
    for (unsigned i = 0; i < num_bits; ++i) {
        m.set(*b1, i, true);
    }
    ENSURE(m.equals(*b1, *b2));
    m.deallocate(b1);
    m.deallocate(b2);
    m.deallocate(b3);
}

void tst_fixed_bit_vector() {
    tst1();
    tst_or();
    tst_and();
    tst_eq(15);
    tst_eq(16);
    tst_eq(17);
    tst_eq(31);
    tst_eq(32);
    tst_eq(33);
    tst_eq(63);
    tst_eq(64);
    tst_eq(65);
}
