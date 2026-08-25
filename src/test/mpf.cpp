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
#include "util/mpf.h"
#include "util/f2n.h"

static void bug_set_int() {
    mpf_manager fm;
    scoped_mpf  a(fm);

    fm.set(a, 11, 53, 3);
    ENSURE(fm.to_double(a) == 3.0);

    fm.set(a, 11, 53, 0);
    ENSURE(fm.to_double(a) == 0.0);

    fm.set(a, 11, 53, -1);
    ENSURE(fm.to_double(a) == -1.0);

    fm.set(a, 11, 53, INT_MAX);
    ENSURE(fm.to_double(a) == (double)INT_MAX);

    fm.set(a, 11, 53, INT_MIN);
    ENSURE(fm.to_double(a) == (double)INT_MIN);

    fm.set(a, 8, 24, 3);
    ENSURE(fm.to_float(a) == 3.0);
    ENSURE(fm.to_double(a) == 3.0);

    fm.set(a, 8, 24, 0);
    ENSURE(fm.to_float(a) == 0.0);
    ENSURE(fm.to_double(a) == 0.0);

    fm.set(a, 8, 24, -1);
    ENSURE(fm.to_float(a) == -1.0);
    ENSURE(fm.to_double(a) == -1.0);    

    fm.set(a, 8, 24, INT_MIN);
    ENSURE(fm.to_float(a) == (float)INT_MIN);

    // CMW: This one depends on the rounding mode, but fm.set(..., int) doesn't have one.
    // fm.set(a, 8, 24, INT_MAX);
    // ENSURE(fm.to_float(a) == (float)INT_MAX);
}

static void bug_set_double() {
    mpf_manager fm;
    scoped_mpf  a(fm);

    fm.set(a, 11, 53, 2.5);
    ENSURE(fm.to_double(a) == 2.5);

    fm.set(a, 11, 53, -42.25);
    ENSURE(fm.to_double(a) == -42.25);

    fm.set(a, 8, 24, (double)2.5);
    ENSURE(fm.to_double(a) == 2.5);

    fm.set(a, 8, 24, (double)-42.25);
    ENSURE(fm.to_double(a) == -42.25);

    fm.set(a, 8, 24, (float)2.5);
    ENSURE(fm.to_float(a) == 2.5);

    fm.set(a, 8, 24, (float)-42.25);
    ENSURE(fm.to_float(a) == -42.25);
}

static void test_to_sbv_mpq() {
    mpf_manager fm;
    scoped_mpf a(fm);
    scoped_mpq r(fm.mpq_manager()), expected(fm.mpq_manager());

    fm.set(a, 11, 53, 2.5);
    fm.to_sbv_mpq(MPF_ROUND_NEAREST_TEVEN, a, r);
    fm.mpq_manager().set(expected, 2);
    ENSURE(fm.mpq_manager().eq(r, expected));
    fm.to_sbv_mpq(MPF_ROUND_NEAREST_TAWAY, a, r);
    fm.mpq_manager().set(expected, 3);
    ENSURE(fm.mpq_manager().eq(r, expected));

    fm.set(a, 63, 24, false, fm.mk_min_exp(63), 0);
    fm.to_sbv_mpq(MPF_ROUND_TOWARD_POSITIVE, a, r);
    ENSURE(fm.mpq_manager().is_one(r));
    fm.to_sbv_mpq(MPF_ROUND_TOWARD_ZERO, a, r);
    ENSURE(fm.mpq_manager().is_zero(r));

    fm.set(a, 63, 24, true, fm.mk_min_exp(63), 0);
    fm.to_sbv_mpq(MPF_ROUND_TOWARD_NEGATIVE, a, r);
    ENSURE(fm.mpq_manager().is_minus_one(r));
    fm.to_sbv_mpq(MPF_ROUND_TOWARD_POSITIVE, a, r);
    ENSURE(fm.mpq_manager().is_zero(r));

    fm.mk_pzero(63, 24, a);
    fm.to_sbv_mpq(MPF_ROUND_TOWARD_POSITIVE, a, r);
    ENSURE(fm.mpq_manager().is_zero(r));
}

void tst_mpf() {
    // enable_trace("mpf_mul_bug");
    bug_set_int();
    bug_set_double();
    test_to_sbv_mpq();
}
