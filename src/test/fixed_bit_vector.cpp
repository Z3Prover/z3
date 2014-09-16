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
#include"fixed_bit_vector.h"
#include"vector.h"


static void tst1() {
    fixed_bit_vector_manager m(30);
    fixed_bit_vector *b;
    b = m.allocate0();
    b->set(0, true);
    b->set(1, false);
    b->set(2, true);
    SASSERT(b->get(0) == true);
    SASSERT(b->get(1) == false);
    SASSERT(b->get(2) == true);
    SASSERT(b->get(3) == false);
    SASSERT(b->get(29) == false);
    m.deallocate(b);
}

static void tst_or() {
    {
        fixed_bit_vector_manager m(10);
        fixed_bit_vector *b1, *b2;
        b1 = m.allocate0();
        b2 = m.allocate0();

        b1->set(4);
        b2->set(8);
        b2->set(3);
        b2->set(2);
        b2->set(1);
        m.display(std::cout, *b1) << "\n";
        m.display(std::cout, *b2) << "\n";
        m.set_or(*b1, *b2);
        m.display(std::cout, *b1) << "\n";
        SASSERT(!m.equals(*b1, *b2));
        b1->unset(4);
        SASSERT(m.equals(*b1, *b2));
        b1->unset(3);
        SASSERT(!m.equals(*b1, *b2));
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

    b1->set(3, true);
    SASSERT(!m.equals(*b1, *b2));
    SASSERT(m.equals(*b2, *b3));

    b3->set(3, true);
    SASSERT(m.equals(*b1, *b3));
    
    b2->set(num_bits-1, true);
    b3->set(num_bits-1);
    b3->unset(3);
    SASSERT(m.equals(*b2, *b3));
    m.fill0(*b1);
    m.set_neg(*b1);
    m.fill1(*b2);
    SASSERT(m.equals(*b1, *b2));
    m.fill0(*b1);
    for (unsigned i = 0; i < num_bits; ++i) {
        b1->set(i, true);
    }
    SASSERT(m.equals(*b1, *b2));
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
