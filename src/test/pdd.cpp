#include "math/dd/dd_pdd.h"

namespace dd {
    static void test1() {
        pdd_manager m(20);
        pdd v0 = m.mk_var(0);
        pdd v1 = m.mk_var(1);
        pdd v2 = m.mk_var(2);
        std::cout << v0 << "\n";
        std::cout << v1 << "\n";
        std::cout << v2 << "\n";
        pdd c1 = v0 * v1 * v2;
        pdd c2 = v2 * v0 * v1;
        std::cout << c1 << "\n";
        SASSERT(c1 == c2);

        c1 = v0 + v1 + v2;
        c2 = v2 + v1 + v0;
        std::cout << c1 << "\n";
        SASSERT(c1 == c2);
    }
}

void tst_pdd() {
    dd::test1();
}
