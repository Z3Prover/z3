/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    rcf.cpp

Abstract:

    Testing RCF module

Author:

    Leonardo (leonardo) 2013-01-04

Notes:

--*/
#include"realclosure.h"

static void tst1() {
    unsynch_mpq_manager qm;
    rcmanager m(qm);
    scoped_rcnumeral a(m);
#if 0
    a = 10;
    std::cout << sym_pp(a) << std::endl;
    std::cout << sym_pp(eps) << std::endl;
    std::cout << interval_pp(a) << std::endl;
    std::cout << interval_pp(eps) << std::endl;
#endif

    scoped_rcnumeral eps(m);
    m.mk_infinitesimal("eps", eps);
    mpq aux;
    qm.set(aux, 1, 3);
    m.set(a, aux);

#if 0    
    std::cout << interval_pp(a) << std::endl;
    std::cout << decimal_pp(eps, 4) << std::endl;
    std::cout << decimal_pp(a) << std::endl;
    std::cout << a + eps << std::endl;
    std::cout << a * eps << std::endl;
    std::cout << (a + eps)*eps - eps << std::endl;
#endif    
    std::cout << interval_pp(a - eps*2) << std::endl;
    std::cout << interval_pp(eps + 1) << std::endl;
    scoped_rcnumeral t(m);
    t = (a - eps*2) / (eps + 1);
    std::cout << t << std::endl;
    std::cout << t * (eps + 1) << std::endl;
    a = 10;
    std::cout << (a + eps > a) << std::endl;
    scoped_rcnumeral pi(m);
    m.mk_pi(pi);
    std::cout << pi + 1 << std::endl;
    std::cout << decimal_pp(pi) << std::endl;
    std::cout << decimal_pp(pi + 1) << std::endl;
    scoped_rcnumeral e(m);
    m.mk_e(e);
    t = e + (pi + 1)*2;
    std::cout << t << std::endl;
    std::cout << decimal_pp(t, 10) << std::endl;
    std::cout << (eps + 1 > 1) << std::endl;
    std::cout << interval_pp((a + eps)/(a - eps)) << std::endl;
}

void tst_rcf() {
    tst1();
}
