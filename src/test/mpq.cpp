/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpq.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-21.

Revision History:

--*/

#include "util/mpq.h"
#include "util/rational.h"
#include "util/timeit.h"
#include <iostream>

static void tst0() {
    synch_mpq_manager m;
    mpq a, b;
    m.set(a, 2, 3);
    m.set(b, 4, 3);
    m.div(a, b, b);
    ENSURE(m.eq(b, m.mk_q(1, 2)));
}

static void tst1() {
    synch_mpq_manager m;
    char const * str = "1002034040050606089383838288182";
    mpz v;
    m.set(v, str);
    std::cout << str << "\n" << m.to_string(v) << "\n";
    mpz v2, v3;
    m.mul(v, m.mk_z(-2), v2);
    std::cout << "*-2 = \n" << m.to_string(v2) << "\n";
    m.add(v, v2, v3);
    m.neg(v3);
    ENSURE(m.eq(v, v3));
    ENSURE(m.le(v, v3));
    ENSURE(m.ge(v, v3));
    ENSURE(m.lt(v2, v));
    ENSURE(m.le(v2, v));
    ENSURE(m.gt(v, v2));
    ENSURE(m.ge(v, v2));
    ENSURE(m.neq(v, v2));
    ENSURE(!m.neq(v, v3));
    m.del(v);
    m.del(v2);
    m.del(v3);
}

#if 0
static void mk_random_num_str(unsigned buffer_sz, char * buffer) {
    unsigned div_pos;
    unsigned sz = (rand() % (buffer_sz-2)) + 1;
    if (rand() % 2 == 0) {
        // integer
        div_pos = sz + 1;
    }
    else {
        div_pos = rand() % sz;
        if (div_pos == 0)
            div_pos++;
    }
    ENSURE(sz < buffer_sz);
    for (unsigned i = 0; i < sz-1; ++i) {
        if (i == div_pos && i < sz-2) {
            buffer[i] = '/';
            i++;
            buffer[i] = '1' + (rand() % 9);
        }
        else {
            buffer[i] = '0' + (rand() % 10);
        }
    }
    buffer[sz-1] = 0;
}
#endif

static void bug1() {
    synch_mpq_manager m;
    mpq a;
    mpq b;
    m.set(a, 2);
    m.set(b, 1, 2);
    m.inv(a, a);
    ENSURE(m.eq(a, b));
}

static void bug2() {
    synch_mpq_manager m;
    mpq a;
    mpq b;
    m.set(a, -2);
    m.set(b, -1, 2);
    m.inv(a, a);
    ENSURE(m.eq(a, b));
}

static void tst2() {
    unsynch_mpq_manager m;
    scoped_mpq a(m);
    m.set(a, 1, 3);
    std::cout << "1/3: ";
    m.display_decimal(std::cout, a, 10);
    std::cout << "\n1/4: ";
    m.set(a, 1, 4);
    m.display_decimal(std::cout, a, 10);
    std::cout << "\n";
}

static void set_str_bug() {
    unsynch_mpq_manager m;
    scoped_mpq a(m);
    scoped_mpq b(m);
    m.set(a, "1.0");
    std::cout << a << "\n";
    m.set(b, 1);
    ENSURE(a == b);
    m.set(a, "1.1");
    std::cout << a << "\n";
    m.set(b, 11, 10);
    ENSURE(a == b);
    m.set(a, "1/3");
    m.set(b, 1, 3);
    std::cout << a << "\n";
    ENSURE(a == b);
}

static void tst_prev_power_2(int64_t n, uint64_t d, unsigned expected) {
    unsynch_mpq_manager m;
    scoped_mpq a(m);
    m.set(a, n, d);
    ENSURE(m.prev_power_of_two(a) == expected);
}

static void tst_prev_power_2() {
    tst_prev_power_2(-10, 1, 0);
    tst_prev_power_2(0, 1, 0);
    tst_prev_power_2(1, 1, 0);
    tst_prev_power_2(2, 1, 1);
    tst_prev_power_2(3, 1, 1);
    tst_prev_power_2(4, 1, 2);
    tst_prev_power_2(5, 1, 2);
    tst_prev_power_2(8, 1, 3);
    tst_prev_power_2(9, 1, 3);
    tst_prev_power_2(9, 2, 2);
    tst_prev_power_2(9, 4, 1);
    tst_prev_power_2(9, 5, 0);
    tst_prev_power_2((1ll << 60) + 1, 1, 60);
    tst_prev_power_2((1ll << 60), 1, 60);
    tst_prev_power_2((1ll << 60) - 1, 1, 59);
    tst_prev_power_2((1ll << 60), 3, 58);
}

template<bool SYNCH>
static void tst_small_arithmetic() {
    mpq_manager<SYNCH> m;
    _scoped_numeral<mpq_manager<SYNCH>> a(m), b(m), c(m), expected(m);
    _scoped_numeral<mpz_manager<SYNCH>> p(m), q(m), n(m), d(m);
    int nums[] = {INT_MIN, INT_MIN + 1, -65537, -1, 0, 1, 65537, INT_MAX - 1, INT_MAX};
    int dens[] = {1, 2, 3, 65537, INT_MAX - 1, INT_MAX};
    for (int an : nums) for (int ad : dens) for (int bn : nums) for (int bd : dens) {
        m.set(a, an, ad);
        m.set(b, bn, bd);
        m.mul(a.get().numerator(), b.get().denominator(), p);
        m.mul(b.get().numerator(), a.get().denominator(), q);
        ENSURE(m.lt(a, b) == m.lt(p, q));
        for (unsigned op = 0; op < 3; ++op) {
            if (op == 2) {
                m.mul(a.get().numerator(), b.get().numerator(), n);
                m.mul(a.get().denominator(), b.get().denominator(), d);
            }
            else {
                if (op == 0)
                    m.add(p, q, n);
                else
                    m.sub(p, q, n);
                m.mul(a.get().denominator(), b.get().denominator(), d);
            }
            m.set(expected, n, d);
            auto apply = [&](mpq const& x, mpq const& y) {
                if (op == 0)
                    m.add(x, y, c);
                else if (op == 1)
                    m.sub(x, y, c);
                else
                    m.mul(x, y, c);
                ENSURE(m.eq(c, expected));
            };
            m.set(c, "18446744073709551617/4294967297");
            apply(a, b);
            m.set(c, a);
            apply(c, b);
            m.set(c, b);
            apply(a, c);
        }
    }
}

template<bool SYNCH>
static void tst_fused_addmul() {
    mpq_manager<SYNCH> m;
    _scoped_numeral<mpq_manager<SYNCH>> a(m), b(m), c(m), result(m), expected(m);
    _scoped_numeral<mpz_manager<SYNCH>> p(m), q(m), n(m), d(m);
    char const* values[] = {
        "0", "1", "-1", "2/3", "-2/3", "3/2", "-4/9",
        "1048575/1048573", "-1048575/1048573",
        "1048576/1048573", "1048573/1048576",
        "-2147483648/2147483647", "2147483647",
        "18446744073709551617/4294967297", "18446744073709551617/9", "2/15"
    };
    for (auto av : values) for (auto bv : values) for (auto cv : values) {
        m.set(a, av);
        m.set(b, bv);
        m.set(c, cv);
        m.mul(b.get().numerator(), c.get().numerator(), p);
        m.mul(p, a.get().denominator(), p);
        m.mul(b.get().denominator(), c.get().denominator(), q);
        m.mul(q, a.get().numerator(), q);
        m.mul(a.get().denominator(), b.get().denominator(), d);
        m.mul(d, c.get().denominator(), d);
        for (bool subtract : {false, true}) {
            if (subtract)
                m.sub(q, p, n);
            else
                m.add(p, q, n);
            m.set(expected, n, d);
            auto check = [&](mpq const& x, mpq const& y, mpq const& z) {
                if (subtract)
                    m.submul(x, y, z, result);
                else
                    m.addmul(x, y, z, result);
                if (!m.eq(result, expected))
                    std::cerr << (subtract ? "submul(" : "addmul(")
                              << av << ", " << bv << ", " << cv << ") = "
                              << m.to_string(result) << ", expected " << m.to_string(expected)
                              << ", synchronized=" << SYNCH << "\n";
                ENSURE(m.eq(result.get().numerator(), expected.get().numerator()));
                ENSURE(m.eq(result.get().denominator(), expected.get().denominator()));
            };
            m.set(result, "18446744073709551617/4294967297");
            check(a, b, c);
            m.set(result, a);
            check(result, b, c);
            m.set(result, b);
            check(a, result, c);
            m.set(result, c);
            check(a, b, result);
        }
    }
    for (auto value : values) {
        rational a(value), result(a);
        rational expected = a + a * a;
        result.addmul(result, result);
        ENSURE(result == expected);
    }
}

void tst_mpq() {
#ifndef SINGLE_THREAD
    tst_fused_addmul<true>();
    tst_small_arithmetic<true>();
#endif
    tst_fused_addmul<false>();
    tst_small_arithmetic<false>();
    tst_prev_power_2();
    set_str_bug();
    bug2();
    bug1();
    tst0();
    tst1();
    tst2();
}
