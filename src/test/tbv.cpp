#include "tbv.h"

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
    SASSERT(!m.equals(*b1,*b0));
    SASSERT(!m.equals(*b1,*bX));
    SASSERT(!m.equals(*b0,*bX));
    m.set_and(*bX,*b0);
    SASSERT(m.equals(*b0,*bX));
    SASSERT(!m.equals(*b1,*bX));
    m.copy(*bX,*b1);
    SASSERT(m.equals(*b1,*bX));
    SASSERT(!m.equals(*b0,*bX));
    m.fillX(*bX);
    VERIFY(m.intersect(*bX,*b0,*bN));
    SASSERT(m.equals(*b0, *bN));
    VERIFY(!m.intersect(*b0,*b1,*bN));
    m.deallocate(b0);
    m.deallocate(b1);
    m.deallocate(bX);
    m.deallocate(bN);
}

void tst_tbv() {
    tst1(31);
    tst1(11);
    tst1(15);
    tst1(16);
    tst1(17);
}
