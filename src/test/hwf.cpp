/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    hwf.cpp

Abstract:

    hwf repros...

Author:

    Leonardo de Moura (leonardo) 2012-08-23.

Revision History:

--*/
#include"hwf.h"
#include"f2n.h"
#include"rational.h"

static void bug_set_double() {
    hwf_manager m;
    hwf a;

    m.set(a, 0.1);
    SASSERT(m.is_regular(a));

    m.set(a, 1.1);
    SASSERT(m.is_regular(a));

    m.set(a, 11.3);
    SASSERT(m.is_regular(a));

    m.set(a, 0.0);
    SASSERT(m.is_regular(a));
}

static void bug_to_rational() {    
    hwf_manager m;
    hwf a;

    unsynch_mpq_manager mq;
    scoped_mpq r(mq);

    double ad, rd;

    m.set(a, 0.0);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, 1.0);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, 1.5);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, 0.875);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, -1.0);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, -1.5);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, -0.875);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
    SASSERT(ad == rd);

    m.set(a, 0.1);
    m.to_rational(a, r);
    ad = m.to_double(a);
    rd = mq.get_double(r);
#ifdef _WINDOWS    
    // CMW: This one depends on the rounding mode,
    // which is implicit in both hwf::set and in mpq::to_double.
    double diff = (ad-rd);
    SASSERT(diff >= -DBL_EPSILON && diff <= DBL_EPSILON);
#endif
}

static void bug_is_int() {
    unsigned raw_val[2] = { 2147483648u, 1077720461u };
    double   val = *(double*)(raw_val);
    std::cout << val << "\n";
    hwf_manager m;
    hwf a;
    m.set(a, val);
    SASSERT(!m.is_int(a));
} 

void tst_hwf() {
    bug_is_int();
    bug_set_double();
    bug_to_rational();
}
