/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    f2n.cpp

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-08-17.

Revision History:

--*/
#include "util/f2n.h"
#include "util/hwf.h"
#include "util/mpf.h"

static void tst1() {
    hwf_manager      hm;
    f2n<hwf_manager> m(hm);
    hwf a, b;
    m.set(a, 11, 3);
    m.floor(a, b);
    std::cout << "floor(11/3): " << m.to_double(b) << "\n";
    m.ceil(a, b);
    std::cout << "ceil(11/3): " << m.to_double(b) << "\n";
    m.set(a, -11, 3);
    m.floor(a, b);
    std::cout << "floor(-11/3): " << m.to_double(b) << "\n";
    m.ceil(a, b);
    std::cout << "ceil(-11/3): " << m.to_double(b) << "\n";
    m.set(a, 11, 1);
    m.floor(a, b);
    std::cout << "floor(11): " << m.to_double(b) << "\n";
    m.ceil(a, b);
    std::cout << "ceil(11): " << m.to_double(b) << "\n";
}

static void tst2() {
    std::cout << "using mpf...\n";
    mpf_manager      fm;
    f2n<mpf_manager> m(fm);
    scoped_mpf a(fm), b(fm);
    m.set(a, 11, 3);
    m.floor(a, b);
    std::cout << "floor(11/3): " << m.to_double(b) << "\n";
    m.ceil(a, b);
    std::cout << "ceil(11/3): " << m.to_double(b) << "\n";
    m.set(a, -11, 3);
    m.floor(a, b);
    std::cout << "floor(-11/3): " << m.to_double(b) << "\n";
    m.ceil(a, b);
    std::cout << "ceil(-11/3): " << m.to_double(b) << "\n";
    m.set(a, 11, 1);
    m.floor(a, b);
    std::cout << "floor(11): " << m.to_double(b) << "\n";
    m.ceil(a, b);
    std::cout << "ceil(11): " << m.to_double(b) << "\n";
}

void tst_f2n() {
    tst1();
    tst2();
}
