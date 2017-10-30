
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/rel/tbv.h"

static void tst1(unsigned num_bits) {
    tbv_manager m(num_bits);
    
    tbv* b1 = m.allocate1();
    tbv* b0 = m.allocate0();
    tbv* bX = m.allocateX();
    tbv* bN = m.allocate(31);
    m.display(std::cout, *b0) << "\n";
    m.display(std::cout, *b1) << "\n";
    m.display(std::cout, *bX) << "\n";
    m.display(std::cout, *bN) << "\n";
    ENSURE(!m.equals(*b1,*b0));
    ENSURE(!m.equals(*b1,*bX));
    ENSURE(!m.equals(*b0,*bX));
    m.set_and(*bX,*b0);
    ENSURE(m.equals(*b0,*bX));
    ENSURE(!m.equals(*b1,*bX));
    m.copy(*bX,*b1);
    ENSURE(m.equals(*b1,*bX));
    ENSURE(!m.equals(*b0,*bX));
    m.fillX(*bX);
    VERIFY(m.intersect(*bX,*b0,*bN));
    ENSURE(m.equals(*b0, *bN));
    VERIFY(!m.intersect(*b0,*b1,*bN));
    m.fill1(*b1);
    bit_vector to_delete;
    to_delete.reserve(num_bits, false);
    tbv_manager m2(num_bits-2);
    to_delete.set(1);
    to_delete.set(3);
    m.set(*b1, 2, BIT_0);
    m.set(*b1, 4, BIT_x);
    tbv_ref b2(m2, m2.project(to_delete, *b1));
    m.display(std::cout, *b1) << " -> ";
    m2.display(std::cout, *b2) << "\n";
    m.deallocate(b0);
    m.deallocate(b1);
    m.deallocate(bX);
    m.deallocate(bN);

}

static void tst0() {
    tbv_manager m(0);
    
    tbv_ref t1(m), t2(m), t3(m);
    t1 = m.allocate1();
    t2 = m.allocate0();
    t3 = m.allocateX();
    m.display(std::cout, *t1) << "\n";
    m.display(std::cout, *t2) << "\n";
    m.display(std::cout, *t3) << "\n";
    ENSURE(m.equals(*t1, *t2));
    ENSURE(m.equals(*t1, *t3));
}

static void tst2(unsigned num_bits) {
    tbv_manager m(num_bits);
    tbv_ref t(m), t2(m);
    for (unsigned i = 0; i < 55; ++i) {
        t = m.allocate(i);
        ENSURE(m.is_well_formed(*t));
        t2 = m.allocate(i+1);
        VERIFY(!m.set_and(*t2, *t));
        ENSURE(!m.is_well_formed(*t2));
    }
}

void tst_tbv() {
    tst0();
    
    tst1(31);
    tst1(11);
    tst1(15);
    tst1(16);
    tst1(17);

    tst2(31);
    tst2(11);
    tst2(15);
    tst2(16);
    tst2(17);
}
