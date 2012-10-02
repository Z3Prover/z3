/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpf.cpp

Abstract:

    mpf repros...

Author:

    Leonardo de Moura (leonardo) 2012-08-21.

Revision History:

--*/
#include"mpf.h"
#include"f2n.h"

static void bug_set_int() {
    mpf_manager fm;
    scoped_mpf  a(fm);

    fm.set(a, 11, 53, 3);
    SASSERT(fm.to_double(a) == 3.0);

    fm.set(a, 11, 53, 0);
    SASSERT(fm.to_double(a) == 0.0);

    fm.set(a, 11, 53, -1);
    SASSERT(fm.to_double(a) == -1.0);

    fm.set(a, 11, 53, INT_MAX);
    SASSERT(fm.to_double(a) == (double)INT_MAX);

    fm.set(a, 11, 53, INT_MIN);
    SASSERT(fm.to_double(a) == (double)INT_MIN);

    fm.set(a, 8, 24, 3);
    SASSERT(fm.to_float(a) == 3.0);
    SASSERT(fm.to_double(a) == 3.0);

    fm.set(a, 8, 24, 0);
    SASSERT(fm.to_float(a) == 0.0);
    SASSERT(fm.to_double(a) == 0.0);

    fm.set(a, 8, 24, -1);
    SASSERT(fm.to_float(a) == -1.0);
    SASSERT(fm.to_double(a) == -1.0);    

    fm.set(a, 8, 24, INT_MIN);
    SASSERT(fm.to_float(a) == (float)INT_MIN);

    // CMW: This one depends on the rounding mode, but fm.set(..., int) doesn't have one.
    // fm.set(a, 8, 24, INT_MAX);
    // SASSERT(fm.to_float(a) == (float)INT_MAX);
}

static void bug_set_double() {
    mpf_manager fm;
    scoped_mpf  a(fm);

    fm.set(a, 11, 53, 2.5);
    SASSERT(fm.to_double(a) == 2.5);

    fm.set(a, 11, 53, -42.25);
    SASSERT(fm.to_double(a) == -42.25);

    fm.set(a, 8, 24, (double)2.5);
    SASSERT(fm.to_double(a) == 2.5);

    fm.set(a, 8, 24, (double)-42.25);
    SASSERT(fm.to_double(a) == -42.25);

    fm.set(a, 8, 24, (float)2.5);
    SASSERT(fm.to_float(a) == 2.5);

    fm.set(a, 8, 24, (float)-42.25);
    SASSERT(fm.to_float(a) == -42.25);
}

void tst_mpf() {
    enable_trace("mpf_mul_bug");
    bug_set_int();
    bug_set_double();
}
