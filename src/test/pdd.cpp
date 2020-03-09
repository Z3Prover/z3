#include "math/dd/dd_pdd.h"

namespace dd {

class test {
public :

    static void hello_world() {
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
        VERIFY(c1 == c2);
        
        c1 = v0 + v1 + v2;
        c2 = v2 + v1 + v0;
        std::cout << c1 << "\n";
        VERIFY(c1 == c2);

        c1 = (v0+v1) * v2;
        c2 = (v0*v2) + (v1*v2);
        std::cout << c1 << "\n";
        VERIFY(c1 == c2);
        c1 = (c1 + 3) + 1;
        c2 = (c2 + 1) + 3;
        std::cout << c1 << "\n";
        VERIFY(c1 == c2);
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
        VERIFY(c3 == c3.reduce(c1));
    }

    static void reduce() {
        std::cout << "\nreduce\n";
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
        VERIFY(r_ef == (c*d) + 3);
        pdd r_fe = m.reduce(f, e);
        std::cout << "result of reduce " << f << " by " << e << " is " << r_fe << "\n" ;
        VERIFY(r_fe == f);

        // test that b*c*d is treated as the leading monomial
        f = b*c*d - d*d;
        r_ef = m.reduce(e, f);
        std::cout << "result of reduce " << e << " by " << f << " is " << r_ef <<  "\n";
        VERIFY(r_ef == (a*b*d*d) + (2*a*b*c) + (d*d) + (b*c) + (c*d) + 3);

        pdd k = d*d + 3*b;
        VERIFY(m.reduce(f, k) == b*c*d + 3*b);
        
    }



    static void large_product() {
        std::cout << "\nlarge_product\n";
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

    static void reset() {
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

    static void canonize() {
        std::cout << "\ncanonize\n";
        pdd_manager m(2);
        pdd a = m.mk_var(0);
        pdd b = m.mk_var(1);

        pdd e = (a - b) * ( a + b);
        pdd f = a * a  - b * b;
        VERIFY(e == f);

        e = (a - b)* (a - b);
        f = a * a - 2 * a * b + b * b;
        VERIFY(e == f);
        e = a - 3;
        e = e * e;
        f = a * a - 6 * a + 9;
        VERIFY(e == f);        
        e = 2 * a - 3;
        e = e * e;
        f = 4 * a * a - 12 * a + 9;
        VERIFY(e == f);        
    }


    static void iterator() {
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
    static void order() {
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
            VERIFY(i != 0 ||( m.vars.size() == 1 && m.vars[0] == vb));
            VERIFY(i != 1 ||( m.vars.size() == 1 && m.vars[0] == va));
            i++;
        }
        pdd ccbbaa = c*c*b*b*a*a;
        pdd ccbbba = c*c*b*b*b*a;
        p = ccbbaa + ccbbba;

        i = 0;
        std::cout << "p = " <<  p << "\n";
        for (auto const& m : p) {
            std::cout << m << "\n";
            VERIFY(i != 0 ||( m.vars.size() == 6 && m.vars[4] == vb)); // the first one has to be ccbbba
            VERIFY(i != 1 ||( m.vars.size() == 6 && m.vars[4] == va)); // the second one has to be ccbbaa
            i++;
        }
        pdd dcbba = d*c*b*b*a;
        pdd dd = d * d;
        p = dcbba + ccbbba + dd;
        vector<unsigned> v;
        std::cout << "p = " <<  p << "\n";
        unsigned k = p.index();
        std::cout << "pdd(k) = " << pdd(k, m) << "\n";
        k = m.first_leading(k);
        do {
            if (m.is_val(k)) {
                VERIFY(m.val(k).is_one());
                break;
            }
            v.push_back(m.var(k));        
            std::cout << "pdd(k) = " << pdd(k, m) << "\n";
            std::cout << "push v" << m.var(k) << "\n";
            k = m.next_leading(k);
        } while(true);
        auto it = v.begin();
        std::cout << "v" << *it;
        it++;
        for( ; it != v.end(); it ++) {
            std::cout << "*v" << *it;
        }
        VERIFY(v.size() == 6);
        VERIFY(v[0] == vc);
        std::cout << "\n";
        v.reset();
        p = d*c*c*d + b*c*c*b + d*d*d;
        k = p.index();
        std::cout << "pdd(k) = " << pdd(k, m) << "\n";
        k = m.first_leading(k);
        do {
            if (m.is_val(k)) {
                VERIFY(m.val(k).is_one());
                break;
            }
            v.push_back(m.var(k));        
            std::cout << "pdd(k) = " << pdd(k, m) << "\n";
            std::cout << "push v" << m.var(k) << "\n";
            k = m.next_leading(k);
        } while(true);
        it = v.begin();
        std::cout << "v" << *it;
        it++;
        for( ; it != v.end(); it ++) {
            std::cout << "*v" << *it;
        }
        VERIFY(v.size() == 4);
        VERIFY(v[0] == vd);
        std::cout << "\n";
    
    }
    static void order_lm() {
        std::cout << "order_lm\n";
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
            VERIFY(i != 0 ||( m.vars.size() == 1 && m.vars[0] == vb));
            VERIFY(i != 1 ||( m.vars.size() == 1 && m.vars[0] == va));
            i++;
        }
        pdd ccbbaa = c*c*b*b*a*a;
        pdd ccbbba = c*c*b*b*b*a;
        p = ccbbaa + ccbbba;

        i = 0;
        std::cout << "p = " <<  p << "\n";
        for (auto const& m : p) {
            std::cout << m << "\n";
            VERIFY(i != 0 ||( m.vars.size() == 6 && m.vars[4] == vb)); // the first one has to be ccbbba
            VERIFY(i != 1 ||( m.vars.size() == 6 && m.vars[4] == va)); // the second one has to be ccbbaa
            i++;
        }
        pdd dcbba = d*c*b*b*a;
        pdd dd = d * d;
        pdd p0 = p + dd;
        std::cout << p0 << " > " << p << "\n";
        VERIFY(m.lm_lt(p, p0));
        VERIFY(m.lm_lt(p0 + a * b, p0 + b * b));
        
    }

};

}

void tst_pdd() {
    dd::test::hello_world();
    dd::test::reduce();
    dd::test::large_product();
    dd::test::canonize();
    dd::test::reset();
    dd::test::iterator();
    dd::test::order();
    dd::test::order_lm();
}
