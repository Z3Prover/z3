#include "math/dd/dd_pdd.h"

namespace dd {
    static void test1() {
        pdd_manager m(3);
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

        c1 = (v0+v1) * v2;
        c2 = (v0*v2) + (v1*v2);
        std::cout << c1 << "\n";
        SASSERT(c1 == c2);
        c1 = (c1 + 3) + 1;
        c2 = (c2 + 1) + 3;
        std::cout << c1 << "\n";
        SASSERT(c1 == c2);
        c1 = v0 - v1;
        c2 = v1 - v0;
        std::cout << c1 << " " << c2 << "\n";

        c1 = v1*v2;
        c2 = (v0*v2) + (v2*v2);
        pdd c3 = m.zero();
        VERIFY(m.try_spoly(c1, c2, c3));
        std::cout << c1 << " " << c2 << " spoly: " << c3 << "\n";

        c1 = v1*v2;
        c2 = (v0*v2) + (v1*v1);
        VERIFY(m.try_spoly(c1, c2, c3));
        std::cout << c1 << " " << c2 << " spoly: " << c3 << "\n";

        c1 = (v0*v1) - (v0*v0);
        c2 = (v0*v1*(v2 + v0)) + v2;
        c3 = c2.reduce(c1);
        std::cout << c1 << " " << c2 << " reduce: " << c3 << "\n";
    }

    static void test2() {
        std::cout << "\ntest2\n";
        // a(b^2)cd + abc + bcd + bc + cd + 3 reduce by  bc
        pdd_manager m(4);
        pdd a = m.mk_var(0);
        pdd b = m.mk_var(1);
        pdd c = m.mk_var(2);
        pdd d = m.mk_var(3);
        pdd e = (a * b * b * c * d) + (2*a*b*c) + (b*c*d) + (b*c) + (c*d) + 3;
        std::cout << e << "\n";
        pdd f = b * c;
        pdd r_ef = m.reduce(e, f);
        m.display(std::cout);
        std::cout << "result of reduce " << e << " by " << f << " is " << r_ef <<  "\n";
        pdd r_fe = m.reduce(f, e);
        std::cout << "result of reduce " << f << " by " << e << " is " << r_fe << "\n" ;
        VERIFY(r_fe == f);
    }

    static void test3() {
        std::cout << "\ntest3\n";
        pdd_manager m(4);
        pdd a = m.mk_var(0);
        pdd b = m.mk_var(1);
        pdd c = m.mk_var(2);
        pdd d = m.mk_var(3);
        
        pdd e = a + c;
        for (unsigned i = 0; i < 5; i++) {
            e = e * e;
        }
        e = e * b;
        std::cout << e << "\n";
    }

    static void test_reset() {
        std::cout << "\ntest reset\n";
        pdd_manager m(4);
        pdd a = m.mk_var(0);
        pdd b = m.mk_var(1);
        pdd c = m.mk_var(2);
        pdd d = m.mk_var(3);
        std::cout << (a + b)*(c + d) << "\n";

        unsigned_vector l2v;
        for (unsigned i = 0; i < 4; ++i) 
            l2v.push_back(3 - i);
        m.reset(l2v);
        a = m.mk_var(0);
        b = m.mk_var(1);
        c = m.mk_var(2);
        d = m.mk_var(3);
        std::cout << (a + b)*(c + d) << "\n";
    }

}

void tst_pdd() {
    dd::test1();
    dd::test2();
    dd::test3();
    dd::test_reset();
}
