/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpbq.cpp

Abstract:

    mpbq tests...

Author:

    Leonardo de Moura (leonardo) 2012-09-20

Revision History:

--*/
#include "util/mpbq.h"

static void tst1() {
    unsynch_mpz_manager zm;
    mpbq_manager m(zm);
    scoped_mpbq  a(m), b(m);
    m.set(a, INT_MAX);
    a = a + 1;
    a = a * a;
    a = a*3 - 1;
    a = a * a - 5;
    a = a * a - 7;
    m.div2k(a, 67);
    std::cout << a << "\n";
    b = a;
    m.approx(b, 32, true);
    std::cout << b << "\n";
    b = a;
    m.approx(b, 32, false);
    std::cout << b << "\n";
    b = a; m.neg(b);
    m.approx(b, 32, true);
    std::cout << b << "\n";
    b = a; m.neg(b);
    m.approx(b, 32, false);
    std::cout << b << "\n";
}

static void tst2() {
   unsynch_mpz_manager zm;
   mpbq_manager m(zm);
   scoped_mpbq  a(m), b(m);
   m.set(a, 5);
   m.set(b, 3);
   m.approx_div(a, b, a, 128);
   std::cout << a << "\n";
 }

void tst_mpbq() {
    tst1();
    tst2();
}
