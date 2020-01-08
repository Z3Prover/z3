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

static void test5() {
    std::cout << "\ntest5\n";
    pdd_manager m(2);
    pdd a = m.mk_var(0);
    pdd b = m.mk_var(1);

    pdd e = (a - b) * ( a + b);
    pdd f = a * a  - b * b;
    SASSERT(e == f);

    e = (a - b)* (a - b);
    f = a * a - 2 * a * b + b * b;
    SASSERT(e == f);
    e = a - 3;
    e = e * e;
    f = a * a - 6 * a + 9;
    SASSERT(e == f);        
    e = 2 * a - 3;
    e = e * e;
    f = 4 * a * a - 12 * a + 9;
    SASSERT(e == f);        
}


void test_iterator() {
    std::cout << "test iterator\n";
    pdd_manager m(4);
    pdd a = m.mk_var(0);
    pdd b = m.mk_var(1);
    pdd c = m.mk_var(2);
    pdd d = m.mk_var(3);
    pdd p = (a + b)*(c + 3*d) + 2;
    std::cout << p << "\n";
    for (auto const& m : p) {
        std::cout << m << "\n";
    }
}

void order() {
    std::cout << "order\n";
    pdd_manager m(4);
    unsigned va = 0;
    unsigned vb = 1;
    unsigned vc = 2;
    unsigned vd = 3;
    pdd a = m.mk_var(va);
    pdd b = m.mk_var(vb);
    pdd c = m.mk_var(vc);
    pdd d = m.mk_var(vd);
    pdd p = a + b;
    std::cout << p << "\n";
    unsigned i = 0;
    for (auto const& m : p) {
        std::cout << m << "\n";        
        SASSERT(i != 0 ||( m.vars.size() == 1 && m.vars[0] == vb));
        SASSERT(i != 1 ||( m.vars.size() == 1 && m.vars[0] == va));
        i++;
        //        SASSERT(i != 1 || m == a);
    }
    pdd ccbbaa = c*c*b*b*a*a;
    pdd ccbbba = c*c*b*b*b*a;
    p = ccbbaa + ccbbba;

    i = 0;
    std::cout << "p = " <<  p << "\n";
    for (auto const& m : p) {
        std::cout << m << "\n";
        SASSERT(i != 0 ||( m.vars.size() == 6 && m.vars[4] == vb)); // the first one has to be ccbbba
        SASSERT(i != 1 ||( m.vars.size() == 6 && m.vars[4] == va)); // the second one has to be ccbbaa
        i++;
        //        SASSERT(i != 1 || m == a);
    }
    pdd dcbba = c*c*b*b*a*a;
    pdd dd = d * d;
    p = dcbba + ccbbba + d;
    std::cout << "p = " <<  p << "\n";
    std::cout << "more complex\n";
    i = 0;
    for (auto const& m : p) {
        std::cout << m << "\n";
        SASSERT(i != 0 ||( m.vars.size() == 6 && m.vars[0] == vc)); // the first one has to be ccbbba
        SASSERT(i != 1 ||( m.vars.size() == 5 && m.vars[0] == vd)); // the second one has to be dcbba
        SASSERT(i != 2 ||( m.vars.size() == 2 && m.vars[1] == vd)); // the second one has to be dd
        
        i++;
        //        SASSERT(i != 1 || m == a);
    }
    
    
}

}

void tst_pdd() {
    dd::test1();
    dd::test2();
    dd::test3();
    dd::test5();
    dd::test_reset();
    dd::test_iterator();
    dd::order();
}
