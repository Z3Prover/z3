#include "math/dd/dd_bdd.h"

namespace dd {
    static void test1() {
        bdd_manager m(20);
        bdd v0 = m.mk_var(0);
        bdd v1 = m.mk_var(1);
        bdd v2 = m.mk_var(2);
        bdd c1 = v0 && v1 && v2;
        bdd c2 = v2 && v0 && v1;
        std::cout << c1 << "\n";
        SASSERT(c1 == c2);
        std::cout << "cnf size: " << c1.cnf_size() << "\n";

        c1 = v0 || v1 || v2;
        c2 = v2 || v1 || v0;
        std::cout << c1 << "\n";
        SASSERT(c1 == c2);
        std::cout << "cnf size: " << c1.cnf_size() << "\n";
    }

    static void test2() {
        bdd_manager m(20);
        bdd v0 = m.mk_var(0);
        bdd v1 = m.mk_var(1);
        bdd v2 = m.mk_var(2);
        SASSERT(m.mk_ite(v0,v0,v1) == (v0 || v1));
        SASSERT(m.mk_ite(v0,v1,v1) == v1);
        SASSERT(m.mk_ite(v1,v0,v1) == (v0 && v1));
        SASSERT(m.mk_ite(v1,v0,v0) == v0);
        SASSERT(m.mk_ite(v0,!v0,v1) == (!v0 && v1));
        SASSERT(m.mk_ite(v0,v1,!v0) == (!v0 || v1));
        SASSERT((!(v0 && v1)) == (!v0 || !v1));
        SASSERT((!(v0 || v1)) == (!v0 && !v1));
    }

    static void test3() {
        bdd_manager m(20);
        bdd v0 = m.mk_var(0);
        bdd v1 = m.mk_var(1);
        bdd v2 = m.mk_var(2);
        bdd c1 = (v0 && v1) || v2;
        bdd c2 = m.mk_exists(0, c1);
        std::cout << c1 << "\n";
        std::cout << c2 << "\n";
        SASSERT(c2 == (v1 || v2));
        c2 = m.mk_exists(1, c1);
        SASSERT(c2 == (v0 || v2));
        c2 = m.mk_exists(2, c1);
        SASSERT(c2.is_true());
        SASSERT(m.mk_exists(3, c1) == c1);
        c1 = (v0 && v1) || (v1 && v2) || (!v0 && !v2);
        c2 = m.mk_exists(0, c1);
        SASSERT(c2 == (v1 || (v1 && v2) || !v2));
        c2 = m.mk_exists(1, c1);
        SASSERT(c2 == (v0 || v2 || (!v0 && !v2)));
        c2 = m.mk_exists(2, c1);
        SASSERT(c2 == ((v0 && v1) || v1 || !v0));
    }

    static void test4() {
        bdd_manager m(3);
        bdd v0 = m.mk_var(0);
        bdd v1 = m.mk_var(1);
        bdd v2 = m.mk_var(2);
        bdd c1 = (v0 && v2) || v1;
        std::cout << "before reorder:\n";
        std::cout << c1 << "\n";
        std::cout << c1.bdd_size() << "\n";
        m.gc();
        m.try_reorder();
        std::cout << "after reorder:\n";
        std::cout << c1 << "\n";
        std::cout << c1.bdd_size() << "\n";
    }

    static void test_xor() {
        bdd_manager m(4);
        bdd v0 = m.mk_var(0);
        bdd v1 = m.mk_var(0);
        SASSERT((m.mk_false() ^ v0) == v0);
        SASSERT((v0 ^ m.mk_false()) == v0);
        SASSERT((m.mk_true() ^ v0) == !v0);
        SASSERT((v0 ^ m.mk_true()) == !v0);
        SASSERT((v0 ^ v1) == ((v0 && !v1) || (!v0 && v1)));
    }

    static void test_int() {
        unsigned const w = 3;  // bit width
        unsigned_vector bits;
        bits.push_back(0);
        bits.push_back(1);
        bits.push_back(2);
        bdd_manager m(w);

        vector<bdd> num;
        for (unsigned n = 0; n < (1<<w); ++n)
            num.push_back(m.mk_int(rational(n), w));
        for (unsigned k = 0; k < (1 << w); ++k) {
            for (unsigned n = 0; n < (1 << w); ++n) {
                SASSERT(num[k].contains_int(rational(n), bits) == (n == k));
                rational r;
                SASSERT_EQ((num[n] || num[k]).find_int(bits, r), (n == k) ? find_int_t::singleton : find_int_t::multiple);
                SASSERT(r == n || r == k);
            }
        }

        bdd s0127 = num[0] || num[1] || num[2] || num[7];
        SASSERT(s0127.contains_int(rational(0), bits));
        SASSERT(s0127.contains_int(rational(1), bits));
        SASSERT(s0127.contains_int(rational(2), bits));
        SASSERT(!s0127.contains_int(rational(3), bits));
        SASSERT(!s0127.contains_int(rational(4), bits));
        SASSERT(!s0127.contains_int(rational(5), bits));
        SASSERT(!s0127.contains_int(rational(6), bits));
        SASSERT(s0127.contains_int(rational(7), bits));

        bdd s123 = num[1] || num[2] || num[3];
        SASSERT((s0127 && s123) == (num[1] || num[2]));

        // larger width constrains additional bits
        SASSERT(m.mk_int(rational(6), 3) != m.mk_int(rational(6), 4));

        // 4*x + 2 == 0 (mod 2^3) has no solutions
        SASSERT(m.mk_affine(rational(4), rational(2), 3).is_false());
        // 3*x + 2 == 0 (mod 2^3) has the unique solution 2
        SASSERT(m.mk_affine(rational(3), rational(2), 3) == num[2]);
        // 2*x + 2 == 0 (mod 2^3) has the solutions 3, 7
        SASSERT(m.mk_affine(rational(2), rational(2), 3) == (num[3] || num[7]));
        // 12*x + 8 == 0 (mod 2^4) has the solutions 2, 6, 10, 14
        bdd expected = m.mk_int(rational(2), 4) || m.mk_int(rational(6), 4) || m.mk_int(rational(10), 4) || m.mk_int(rational(14), 4);
        SASSERT(m.mk_affine(rational(12), rational(8), 4) == expected);

        SASSERT(m.mk_affine(rational(0), rational(0), 3).is_true());
        SASSERT(m.mk_affine(rational(0), rational(1), 3).is_false());
        // 2*x == 0 (mod 2^3) has the solutions 0, 4
        SASSERT(m.mk_affine(rational(2), rational(0), 3) == (num[0] || num[4]));
    }
}

void tst_bdd() {
    dd::test1();
    dd::test2();
    dd::test3();
    dd::test4();
    dd::test_xor();
    dd::test_int();
}
