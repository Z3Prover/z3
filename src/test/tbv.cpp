
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

#if 0
// prints all don't care pareto fronts for 8-bit multiplier.
static void test_dc() {
    unsigned num_bits = 8;
    unsigned num_vals = 1 << num_bits;
    tbv_manager m(num_bits*2);
    tbv::eq eq(m);
    tbv::hash hash(m);
    ptr_vector<tbv> tbvs, todo;
    map<tbv*, tbit, tbv::hash, tbv::eq> eval(hash, eq);

    for (unsigned a = 0; a < num_vals; ++a) {
        for (unsigned b = 0; b < num_vals; ++b) {
            unsigned c = a*b;
            unsigned bits = a + (b << num_bits); 
            bool value = (c & (1 << (num_bits-1))) != 0;
            tbv* t = m.allocate(bits);
            tbvs.push_back(t);
            eval.insert(t, value ? BIT_1 : BIT_0);
            todo.push_back(t);
        }
    }
    std::cout << todo.size() << "\n";
    for (unsigned i = 0; i < todo.size(); ++i) {
        tbv* t = todo[i];
        todo.pop_back();
        bool found = false;
        tbit tvalue = eval[t];
        SASSERT(tvalue != BIT_z);
        for (unsigned j = 0; j < 2*num_bits; ++j) {
            tbit tb = (*t)[j];
            if (tb == BIT_x)
                continue;
            tbv* nt = m.allocate(*t);
            tbvs.push_back(nt);
            m.set(*nt, j, neg(tb));
            if (!eval.contains(nt))
                continue;
            tbit nvalue = eval[nt];
            m.set(*nt, j, BIT_x);
            if (eval.contains(nt))
                continue;
            if (tvalue == nvalue) {
                todo.push_back(nt);
                eval.insert(nt, tvalue);                
                found = true;
            }
            else 
                eval.insert(nt, BIT_z);
        }
        if (!found) 
            m.display(std::cout, *t) << " := " << (eval[t] == BIT_0 ? 0 : 1) << "\n";
    }


    for (auto* t : tbvs)
        m.deallocate(t);
    
}
#endif

void tst_tbv() {
    // test_dc();
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
