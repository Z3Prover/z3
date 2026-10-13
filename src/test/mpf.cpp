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

static void test_set_extreme_exponents() {
    mpf_manager fm;
    scoped_mpf a(fm), expected(fm);
    scoped_mpz exponent(fm.mpz_manager());
    scoped_mpq significand(fm.mpq_manager());
    mpf_rounding_mode modes[] = {
        MPF_ROUND_NEAREST_TEVEN, MPF_ROUND_NEAREST_TAWAY,
        MPF_ROUND_TOWARD_POSITIVE, MPF_ROUND_TOWARD_NEGATIVE,
        MPF_ROUND_TOWARD_ZERO
    };
    char const * exponents[] = {
        "2147483647", "2147483648", "3000000000",
        "9223372036854775807", "9223372036854775808",
        "18446744073709551616"
    };
    for (auto rm : modes) {
        for (bool sign : { false, true }) {
            fm.mpq_manager().set(significand, sign ? -1 : 1);
            for (auto e : exponents) {
                fm.mpz_manager().set(exponent, e);
                fm.set(a, 11, 53, rm, exponent, significand);
                bool finite = rm == MPF_ROUND_TOWARD_ZERO ||
                    rm == (sign ? MPF_ROUND_TOWARD_POSITIVE : MPF_ROUND_TOWARD_NEGATIVE);
                if (finite)
                    fm.mk_max_value(11, 53, sign, expected);
                else
                    fm.mk_inf(11, 53, sign, expected);
                ENSURE(fm.eq(a, expected));
                ENSURE(fm.is_neg(a) == sign);

                fm.mpz_manager().neg(exponent);
                fm.set(a, 11, 53, rm, exponent, significand);
                bool subnormal = rm ==
                    (sign ? MPF_ROUND_TOWARD_NEGATIVE : MPF_ROUND_TOWARD_POSITIVE);
                fm.set(expected, 11, 53, sign, fm.mk_bot_exp(11), subnormal ? 1 : 0);
                ENSURE(fm.eq(a, expected));
                ENSURE(fm.is_neg(a) == sign);
            }
        }
    }

    for (bool sign : { false, true }) {
        fm.set(a, 11, 53, MPF_ROUND_NEAREST_TEVEN,
               sign ? "-1p-3000000000" : "1p-3000000000");
        ENSURE(fm.is_zero(a));
        ENSURE(fm.is_neg(a) == sign);

        fm.mpq_manager().set(significand, sign ? -1 : 1);
        for (int64_t e : { INT64_C(-3000000000), INT64_C(3000000000) }) {
            fm.mpz_manager().set(exponent, e);
            fm.set(a, 63, 53, MPF_ROUND_NEAREST_TEVEN, exponent, significand);
            fm.set(expected, 63, 53, sign, e, 0);
            ENSURE(fm.eq(a, expected));
        }
    }

    fm.mpq_manager().set(significand, 0);
    fm.mpz_manager().set(exponent, "-18446744073709551616");
    fm.set(a, 11, 53, MPF_ROUND_NEAREST_TEVEN, exponent, significand);
    ENSURE(fm.is_zero(a));
}

void tst_mpf() {
    // enable_trace("mpf_mul_bug");
    bug_set_int();
    bug_set_double();
    test_to_sbv_mpq();
    test_set_extreme_exponents();
}
