/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpfx.cpp

Abstract:

    Multi precision fixed point numbers.
    
Author:

    Leonardo de Moura (leonardo) 2012-09-19

Revision History:

--*/
#include"mpfx.h"

static void tst1() {
    mpfx_manager m;
    scoped_mpfx a(m), b(m), c(m);
    m.set(a, 1);
    m.set(b, 2);
    std::cout << a << " + " << b << " == " << (a+b) << "\n";
    m.set(a, 5);
    m.set(c, 3);
    m.display_raw(std::cout, (a*a*b)/c); std::cout << "\n";
    m.display_decimal(std::cout, (a*a*b)/c); std::cout << "\n";
    m.display_decimal(std::cout, (a*a*b)/c, 10); std::cout << "\n";
    m.round_to_plus_inf();
    m.display_decimal(std::cout, (a*a*b)/c); std::cout << "\n";
    m.set(a, -1, 4);
    m.display_decimal(std::cout, a); std::cout << "\n";
}

static void tst_prev_power_2(int64 n, uint64 d, unsigned expected) {
    mpfx_manager m;
    scoped_mpfx a(m);
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

void tst_mpfx() {
    tst_prev_power_2();
    tst1();
}
