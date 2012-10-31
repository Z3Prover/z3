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

#include"mpq.h"
#include"rational.h"
#include"timeit.h"

static void tst0() {
    synch_mpq_manager m;
    mpq a, b;
    m.set(a, 2, 3);
    m.set(b, 4, 3);
    m.div(a, b, b);
    SASSERT(m.eq(b, m.mk_q(1, 2)));
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
    SASSERT(m.eq(v, v3));
    SASSERT(m.le(v, v3));
    SASSERT(m.ge(v, v3));
    SASSERT(m.lt(v2, v));
    SASSERT(m.le(v2, v));
    SASSERT(m.gt(v, v2));
    SASSERT(m.ge(v, v2));
    SASSERT(m.neq(v, v2));
    SASSERT(!m.neq(v, v3));
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
    SASSERT(sz < buffer_sz);
    for (unsigned i = 0; i < sz-1; i++) {
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
    SASSERT(m.eq(a, b));
}

static void bug2() {
    synch_mpq_manager m;
    mpq a;
    mpq b;
    m.set(a, -2);
    m.set(b, -1, 2);
    m.inv(a, a);
    SASSERT(m.eq(a, b));
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
    SASSERT(a == b);
    m.set(a, "1.1");
    std::cout << a << "\n";
    m.set(b, 11, 10);
    SASSERT(a == b);
    m.set(a, "1/3");
    m.set(b, 1, 3);
    std::cout << a << "\n";
    SASSERT(a == b);
}

static void tst_prev_power_2(int64 n, uint64 d, unsigned expected) {
    unsynch_mpq_manager m;
    scoped_mpq a(m);
    m.set(a, n, d);
    SASSERT(m.prev_power_of_two(a) == expected);
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

void tst_mpq() {
    tst_prev_power_2();
    set_str_bug();
    bug2();
    bug1();
    tst0();
    tst1();
    tst2();
}


