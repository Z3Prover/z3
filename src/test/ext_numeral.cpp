/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ext_numeral.cpp

Abstract:

    Unit tests for ext_numeral template.

Author:

    Leonardo (leonardo) 2012-07-18

Notes:

--*/
#include<sstream>
#include "util/mpq.h"
#include "util/ext_numeral.h"

#define MK_TST_UNARY(NAME)                                              \
static void tst_ ## NAME(int a, ext_numeral_kind ak, int expected_c, ext_numeral_kind expected_ck) { \
    unsynch_mpq_manager m;                                              \
    scoped_mpq _a(m);                                                   \
    m.set(_a, a);                                                       \
    NAME(m, _a, ak);                                                    \
    ENSURE(ak == expected_ck);                                         \
    if (expected_ck == EN_NUMERAL) {                                    \
        scoped_mpq _expected_c(m);                                      \
        m.set(_expected_c, expected_c);                                 \
        ENSURE(m.eq(_a, _expected_c));                                 \
    }                                                                   \
}

MK_TST_UNARY(neg);
MK_TST_UNARY(inv);

#define MK_TST_BIN_CORE(FUN_NAME, OP_NAME)                              \
static void FUN_NAME(int a, ext_numeral_kind ak, int b, ext_numeral_kind bk, int expected_c, ext_numeral_kind expected_ck) { \
    unsynch_mpq_manager m;                                              \
    scoped_mpq _a(m), _b(m), _c(m);                                     \
    m.set(_a, a);                                                       \
    m.set(_b, b);                                                       \
    ext_numeral_kind ck(EN_NUMERAL);                                    \
    OP_NAME(m, _a, ak, _b, bk, _c, ck);                                 \
    ENSURE(ck == expected_ck);                                          \
    if (expected_ck == EN_NUMERAL) {                                    \
        scoped_mpq _expected_c(m);                                      \
        m.set(_expected_c, expected_c);                                 \
        ENSURE(m.eq(_c, _expected_c));                                  \
    }                                                                   \
}

#define MK_TST_BIN(NAME) MK_TST_BIN_CORE(tst_ ## NAME, NAME)

#define MK_TST_COMM_BIN(NAME)                                           \
MK_TST_BIN_CORE(tst_ ## NAME ## _core, NAME)                            \
static void tst_ ## NAME(int a, ext_numeral_kind ak, int b, ext_numeral_kind bk, int expected_c, ext_numeral_kind expected_ck) { \
    tst_ ## NAME ## _core(a, ak, b, bk, expected_c, expected_ck);       \
    tst_ ## NAME ## _core(b, bk, a, ak, expected_c, expected_ck);       \
}

MK_TST_COMM_BIN(add);
MK_TST_BIN(sub);
MK_TST_COMM_BIN(mul);

static void tst1() {
    tst_neg(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_neg(30, EN_MINUS_INFINITY, 10, EN_PLUS_INFINITY);
    tst_neg(0, EN_NUMERAL, 0, EN_NUMERAL);
    tst_neg(10, EN_NUMERAL, -10, EN_NUMERAL);
    tst_neg(-7, EN_NUMERAL, 7, EN_NUMERAL);
    tst_neg(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_neg(30, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_neg(-7, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY);

    tst_inv(0, EN_MINUS_INFINITY, 0, EN_NUMERAL);
    tst_inv(0, EN_PLUS_INFINITY, 0, EN_NUMERAL);
    tst_inv(1, EN_NUMERAL, 1, EN_NUMERAL);
    tst_inv(-1, EN_NUMERAL, -1, EN_NUMERAL);

    tst_add(0, EN_MINUS_INFINITY, 0, EN_MINUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_add(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_add(0, EN_MINUS_INFINITY, -1, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_add(0, EN_MINUS_INFINITY, 1, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_add(1, EN_MINUS_INFINITY, -1, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_add(1, EN_NUMERAL, 0, EN_MINUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_add(-1, EN_NUMERAL, 0, EN_MINUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_add(0, EN_NUMERAL, 0, EN_MINUS_INFINITY, 0, EN_MINUS_INFINITY);

    tst_add(0, EN_NUMERAL, 2, EN_NUMERAL, 2, EN_NUMERAL);
    tst_add(-3, EN_NUMERAL, 4, EN_NUMERAL, 1, EN_NUMERAL);
    tst_add(-2, EN_NUMERAL, 0, EN_NUMERAL, -2, EN_NUMERAL);
    tst_add(3, EN_NUMERAL, 4, EN_NUMERAL, 7, EN_NUMERAL);
    
    tst_add(0, EN_PLUS_INFINITY, 0, EN_PLUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_add(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_add(0, EN_PLUS_INFINITY, 1, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_add(0, EN_PLUS_INFINITY, -1, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_add(0, EN_NUMERAL, 0, EN_PLUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_add(-1, EN_NUMERAL, 0, EN_PLUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_add(1, EN_NUMERAL, 0, EN_PLUS_INFINITY, 0, EN_PLUS_INFINITY);

    tst_mul(0, EN_MINUS_INFINITY, 0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_mul(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY,  0, EN_MINUS_INFINITY);
    tst_mul(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY,  0, EN_MINUS_INFINITY);
    tst_mul(0, EN_PLUS_INFINITY, 0, EN_PLUS_INFINITY,  0,  EN_PLUS_INFINITY);

    tst_mul(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, 0, EN_NUMERAL);
    tst_mul(0, EN_MINUS_INFINITY, 1, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_mul(0, EN_MINUS_INFINITY, 5, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_mul(0, EN_MINUS_INFINITY, -1, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_mul(0, EN_MINUS_INFINITY, -5, EN_NUMERAL, 0, EN_PLUS_INFINITY);

    tst_mul(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, 0, EN_NUMERAL);
    tst_mul(0, EN_PLUS_INFINITY, 1, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_mul(0, EN_PLUS_INFINITY, 5, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_mul(0, EN_PLUS_INFINITY, -1, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_mul(0, EN_PLUS_INFINITY, -5, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    
    tst_mul(0, EN_NUMERAL, 3, EN_NUMERAL, 0, EN_NUMERAL);
    tst_mul(2, EN_NUMERAL, 3, EN_NUMERAL, 6, EN_NUMERAL);
    tst_mul(-2, EN_NUMERAL, 3, EN_NUMERAL, -6, EN_NUMERAL);

    tst_sub(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_sub(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_sub(0, EN_PLUS_INFINITY, -10, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_sub(0, EN_PLUS_INFINITY, 10, EN_NUMERAL, 0, EN_PLUS_INFINITY);

    tst_sub(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_sub(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_sub(0, EN_MINUS_INFINITY, -10, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_sub(0, EN_MINUS_INFINITY, 10, EN_NUMERAL, 0, EN_MINUS_INFINITY);

    tst_sub(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY);
    tst_sub(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_sub(0, EN_MINUS_INFINITY, 3, EN_NUMERAL, 0, EN_MINUS_INFINITY);
    tst_sub(0, EN_MINUS_INFINITY, -3, EN_NUMERAL, 0, EN_MINUS_INFINITY);

    tst_sub(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY);
    tst_sub(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_sub(0, EN_PLUS_INFINITY, 3, EN_NUMERAL, 0, EN_PLUS_INFINITY);
    tst_sub(0, EN_PLUS_INFINITY, -3, EN_NUMERAL, 0, EN_PLUS_INFINITY);

    tst_sub(0, EN_NUMERAL, 2, EN_NUMERAL, -2, EN_NUMERAL);
    tst_sub(3, EN_NUMERAL, 2, EN_NUMERAL, 1, EN_NUMERAL);
    tst_sub(3, EN_NUMERAL, -3, EN_NUMERAL, 6, EN_NUMERAL);
    tst_sub(3, EN_NUMERAL, 3, EN_NUMERAL, 0, EN_NUMERAL);
    tst_sub(3, EN_NUMERAL, 0, EN_NUMERAL, 3, EN_NUMERAL);
    tst_sub(-3, EN_NUMERAL, -5, EN_NUMERAL, 2, EN_NUMERAL);
}

#define MK_TST_REL_CORE(FUN_NAME, OP_NAME)                              \
static void FUN_NAME(int a, ext_numeral_kind ak, int b, ext_numeral_kind bk, bool expected)  { \
    unsynch_mpq_manager m;                                              \
    scoped_mpq _a(m), _b(m);                                            \
    m.set(_a, a);                                                       \
    m.set(_b, b);                                                       \
    VERIFY(expected == OP_NAME(m, _a, ak, _b, bk));                     \
}

#define MK_TST_REL(NAME) MK_TST_REL_CORE(tst_ ## NAME, NAME)

#define MK_TST_SYMM_REL(NAME)                                           \
MK_TST_REL_CORE(tst_ ## NAME ## _core, NAME)                            \
static void tst_ ## NAME(int a, ext_numeral_kind ak, int b, ext_numeral_kind bk, bool expected)  { \
    tst_ ## NAME ## _core(a, ak, b, bk, expected);                      \
    tst_ ## NAME ## _core(b, bk, a, ak, expected);                      \
}

MK_TST_SYMM_REL(eq);
MK_TST_SYMM_REL(neq);
MK_TST_REL(lt);
MK_TST_REL(gt);
MK_TST_REL(le);
MK_TST_REL(ge);

static void tst2() {
    tst_eq(0, EN_NUMERAL, 0, EN_NUMERAL, true);
    tst_eq(0, EN_NUMERAL, 2, EN_NUMERAL, false);
    tst_eq(3, EN_NUMERAL, 0, EN_NUMERAL, false);
    tst_eq(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, false);
    tst_eq(0, EN_PLUS_INFINITY, 3, EN_NUMERAL, false);
    tst_eq(0, EN_PLUS_INFINITY, -2, EN_NUMERAL, false);
    tst_eq(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, false);

    tst_neq(0, EN_NUMERAL, 0, EN_NUMERAL, false);
    tst_neq(0, EN_NUMERAL, 2, EN_NUMERAL, true);
    tst_neq(3, EN_NUMERAL, 0, EN_NUMERAL, true);
    tst_neq(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, true);
    tst_neq(0, EN_PLUS_INFINITY, 3, EN_NUMERAL, true);
    tst_neq(0, EN_PLUS_INFINITY, -2, EN_NUMERAL, true);
    tst_neq(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, true);

    tst_lt(0, EN_MINUS_INFINITY, 10, EN_NUMERAL, true);
    tst_lt(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, true);
    tst_lt(0, EN_MINUS_INFINITY, -3, EN_NUMERAL, true);
    tst_lt(30, EN_MINUS_INFINITY, 10, EN_NUMERAL, true);
    tst_lt(20, EN_MINUS_INFINITY, 0, EN_NUMERAL, true);
    tst_lt(-20, EN_MINUS_INFINITY, -3, EN_NUMERAL, true);
    tst_lt(0, EN_MINUS_INFINITY, 10, EN_PLUS_INFINITY, true);
    tst_lt(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY, true);
    tst_lt(10, EN_MINUS_INFINITY, -30, EN_PLUS_INFINITY, true);

    tst_lt(0, EN_PLUS_INFINITY, 10, EN_NUMERAL, false);
    tst_lt(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, false);
    tst_lt(0, EN_PLUS_INFINITY, -3, EN_NUMERAL, false);
    tst_lt(30, EN_PLUS_INFINITY, 10, EN_NUMERAL, false);
    tst_lt(20, EN_PLUS_INFINITY, 0, EN_NUMERAL, false);
    tst_lt(-20, EN_PLUS_INFINITY, -3, EN_NUMERAL, false);
    tst_lt(0, EN_PLUS_INFINITY, 10, EN_MINUS_INFINITY, false);
    tst_lt(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, false);
    tst_lt(10, EN_PLUS_INFINITY, -30, EN_MINUS_INFINITY, false);

    tst_lt(0, EN_NUMERAL, 0, EN_PLUS_INFINITY, true);
    tst_lt(20, EN_NUMERAL, 10, EN_PLUS_INFINITY, true);
    tst_lt(-20, EN_NUMERAL, -100, EN_PLUS_INFINITY, true);
    tst_lt(0, EN_NUMERAL, 10, EN_NUMERAL, true);
    tst_lt(0, EN_NUMERAL, 0, EN_NUMERAL, false);
    tst_lt(10, EN_NUMERAL, 10, EN_NUMERAL, false);
    tst_lt(0, EN_NUMERAL, -3, EN_NUMERAL, false);
    tst_lt(30, EN_NUMERAL, 10, EN_NUMERAL, false);
    tst_lt(30, EN_NUMERAL, 40, EN_NUMERAL, true);
    tst_lt(20, EN_NUMERAL, 0, EN_NUMERAL, false);
    tst_lt(-20, EN_NUMERAL, -3, EN_NUMERAL, true);
    tst_lt(0, EN_NUMERAL, 10, EN_MINUS_INFINITY, false);
    tst_lt(0, EN_NUMERAL, 0, EN_MINUS_INFINITY, false);
    tst_lt(10, EN_NUMERAL, -30, EN_MINUS_INFINITY, false);

    tst_le(0, EN_MINUS_INFINITY, 10, EN_NUMERAL, true);
    tst_le(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, true);
    tst_le(0, EN_MINUS_INFINITY, -3, EN_NUMERAL, true);
    tst_le(30, EN_MINUS_INFINITY, 10, EN_NUMERAL, true);
    tst_le(20, EN_MINUS_INFINITY, 0, EN_NUMERAL, true);
    tst_le(-20, EN_MINUS_INFINITY, -3, EN_NUMERAL, true);
    tst_le(0, EN_MINUS_INFINITY, 10, EN_PLUS_INFINITY, true);
    tst_le(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY, true);
    tst_le(10, EN_MINUS_INFINITY, -30, EN_PLUS_INFINITY, true);

    tst_le(0, EN_PLUS_INFINITY, 10, EN_NUMERAL, false);
    tst_le(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, false);
    tst_le(0, EN_PLUS_INFINITY, -3, EN_NUMERAL, false);
    tst_le(30, EN_PLUS_INFINITY, 10, EN_NUMERAL, false);
    tst_le(20, EN_PLUS_INFINITY, 0, EN_NUMERAL, false);
    tst_le(-20, EN_PLUS_INFINITY, -3, EN_NUMERAL, false);
    tst_le(0, EN_PLUS_INFINITY, 10, EN_MINUS_INFINITY, false);
    tst_le(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, false);
    tst_le(10, EN_PLUS_INFINITY, -30, EN_MINUS_INFINITY, false);

    tst_le(0, EN_NUMERAL, 0, EN_PLUS_INFINITY, true);
    tst_le(20, EN_NUMERAL, 10, EN_PLUS_INFINITY, true);
    tst_le(-20, EN_NUMERAL, -100, EN_PLUS_INFINITY, true);
    tst_le(0, EN_NUMERAL, 10, EN_NUMERAL, true);
    tst_le(0, EN_NUMERAL, 0, EN_NUMERAL, true);
    tst_le(10, EN_NUMERAL, 10, EN_NUMERAL, true);
    tst_le(0, EN_NUMERAL, -3, EN_NUMERAL, false);
    tst_le(30, EN_NUMERAL, 10, EN_NUMERAL, false);
    tst_le(30, EN_NUMERAL, 40, EN_NUMERAL, true);
    tst_le(20, EN_NUMERAL, 0, EN_NUMERAL, false);
    tst_le(-20, EN_NUMERAL, -3, EN_NUMERAL, true);
    tst_le(0, EN_NUMERAL, 10, EN_MINUS_INFINITY, false);
    tst_le(0, EN_NUMERAL, 0, EN_MINUS_INFINITY, false);
    tst_le(10, EN_NUMERAL, -30, EN_MINUS_INFINITY, false);


    tst_ge(0, EN_MINUS_INFINITY, 10, EN_NUMERAL, false);
    tst_ge(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, false);
    tst_ge(0, EN_MINUS_INFINITY, -3, EN_NUMERAL, false);
    tst_ge(30, EN_MINUS_INFINITY, 10, EN_NUMERAL, false);
    tst_ge(20, EN_MINUS_INFINITY, 0, EN_NUMERAL, false);
    tst_ge(-20, EN_MINUS_INFINITY, -3, EN_NUMERAL, false);
    tst_ge(0, EN_MINUS_INFINITY, 10, EN_PLUS_INFINITY, false);
    tst_ge(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY, false);
    tst_ge(10, EN_MINUS_INFINITY, -30, EN_PLUS_INFINITY, false);

    tst_ge(0, EN_PLUS_INFINITY, 10, EN_NUMERAL, true);
    tst_ge(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, true);
    tst_ge(0, EN_PLUS_INFINITY, -3, EN_NUMERAL, true);
    tst_ge(30, EN_PLUS_INFINITY, 10, EN_NUMERAL, true);
    tst_ge(20, EN_PLUS_INFINITY, 0, EN_NUMERAL, true);
    tst_ge(-20, EN_PLUS_INFINITY, -3, EN_NUMERAL, true);
    tst_ge(0, EN_PLUS_INFINITY, 10, EN_MINUS_INFINITY, true);
    tst_ge(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, true);
    tst_ge(10, EN_PLUS_INFINITY, -30, EN_MINUS_INFINITY, true);

    tst_ge(0, EN_NUMERAL, 0, EN_PLUS_INFINITY, false);
    tst_ge(20, EN_NUMERAL, 10, EN_PLUS_INFINITY, false);
    tst_ge(-20, EN_NUMERAL, -100, EN_PLUS_INFINITY, false);
    tst_ge(0, EN_NUMERAL, 10, EN_NUMERAL, false);
    tst_ge(0, EN_NUMERAL, 0, EN_NUMERAL, true);
    tst_ge(10, EN_NUMERAL, 10, EN_NUMERAL, true);
    tst_ge(0, EN_NUMERAL, -3, EN_NUMERAL, true);
    tst_ge(30, EN_NUMERAL, 10, EN_NUMERAL, true);
    tst_ge(30, EN_NUMERAL, 40, EN_NUMERAL, false);
    tst_ge(20, EN_NUMERAL, 0, EN_NUMERAL, true);
    tst_ge(-20, EN_NUMERAL, -3, EN_NUMERAL, false);
    tst_ge(0, EN_NUMERAL, 10, EN_MINUS_INFINITY, true);
    tst_ge(0, EN_NUMERAL, 0, EN_MINUS_INFINITY, true);
    tst_ge(10, EN_NUMERAL, -30, EN_MINUS_INFINITY, true);


    tst_gt(0, EN_MINUS_INFINITY, 10, EN_NUMERAL, false);
    tst_gt(0, EN_MINUS_INFINITY, 0, EN_NUMERAL, false);
    tst_gt(0, EN_MINUS_INFINITY, -3, EN_NUMERAL, false);
    tst_gt(30, EN_MINUS_INFINITY, 10, EN_NUMERAL, false);
    tst_gt(20, EN_MINUS_INFINITY, 0, EN_NUMERAL, false);
    tst_gt(-20, EN_MINUS_INFINITY, -3, EN_NUMERAL, false);
    tst_gt(0, EN_MINUS_INFINITY, 10, EN_PLUS_INFINITY, false);
    tst_gt(0, EN_MINUS_INFINITY, 0, EN_PLUS_INFINITY, false);
    tst_gt(10, EN_MINUS_INFINITY, -30, EN_PLUS_INFINITY, false);

    tst_gt(0, EN_PLUS_INFINITY, 10, EN_NUMERAL, true);
    tst_gt(0, EN_PLUS_INFINITY, 0, EN_NUMERAL, true);
    tst_gt(0, EN_PLUS_INFINITY, -3, EN_NUMERAL, true);
    tst_gt(30, EN_PLUS_INFINITY, 10, EN_NUMERAL, true);
    tst_gt(20, EN_PLUS_INFINITY, 0, EN_NUMERAL, true);
    tst_gt(-20, EN_PLUS_INFINITY, -3, EN_NUMERAL, true);
    tst_gt(0, EN_PLUS_INFINITY, 10, EN_MINUS_INFINITY, true);
    tst_gt(0, EN_PLUS_INFINITY, 0, EN_MINUS_INFINITY, true);
    tst_gt(10, EN_PLUS_INFINITY, -30, EN_MINUS_INFINITY, true);

    tst_gt(0, EN_NUMERAL, 0, EN_PLUS_INFINITY, false);
    tst_gt(20, EN_NUMERAL, 10, EN_PLUS_INFINITY, false);
    tst_gt(-20, EN_NUMERAL, -100, EN_PLUS_INFINITY, false);
    tst_gt(0, EN_NUMERAL, 10, EN_NUMERAL, false);
    tst_gt(0, EN_NUMERAL, 0, EN_NUMERAL, false);
    tst_gt(10, EN_NUMERAL, 10, EN_NUMERAL, false);
    tst_gt(0, EN_NUMERAL, -3, EN_NUMERAL, true);
    tst_gt(30, EN_NUMERAL, 10, EN_NUMERAL, true);
    tst_gt(30, EN_NUMERAL, 40, EN_NUMERAL, false);
    tst_gt(20, EN_NUMERAL, 0, EN_NUMERAL, true);
    tst_gt(-20, EN_NUMERAL, -3, EN_NUMERAL, false);
    tst_gt(0, EN_NUMERAL, 10, EN_MINUS_INFINITY, true);
    tst_gt(0, EN_NUMERAL, 0, EN_MINUS_INFINITY, true);
    tst_gt(10, EN_NUMERAL, -30, EN_MINUS_INFINITY, true);
}

static void tst3() {
    unsynch_mpq_manager m; 
    scoped_mpq a(m);      
    ENSURE(is_zero(m, a, EN_NUMERAL));
    ENSURE(!is_zero(m, a, EN_PLUS_INFINITY));
    ENSURE(!is_zero(m, a, EN_MINUS_INFINITY));
    ENSURE(!is_pos(m, a, EN_NUMERAL));
    ENSURE(is_pos(m, a, EN_PLUS_INFINITY));
    ENSURE(!is_pos(m, a, EN_MINUS_INFINITY));
    ENSURE(!is_infinite(EN_NUMERAL));
    ENSURE(is_infinite(EN_PLUS_INFINITY));
    ENSURE(is_infinite(EN_MINUS_INFINITY));
    ENSURE(!is_neg(m, a, EN_NUMERAL));
    ENSURE(!is_neg(m, a, EN_PLUS_INFINITY));
    ENSURE(is_neg(m, a, EN_MINUS_INFINITY));
    m.set(a, 10);
    ENSURE(!is_zero(m, a, EN_NUMERAL));
    ENSURE(is_pos(m, a, EN_NUMERAL));
    ENSURE(!is_neg(m, a, EN_NUMERAL));
    ENSURE(!is_infinite(EN_NUMERAL));
    m.set(a, -5);
    ENSURE(!is_zero(m, a, EN_NUMERAL));
    ENSURE(!is_pos(m, a, EN_NUMERAL));
    ENSURE(is_neg(m, a, EN_NUMERAL));
    ENSURE(!is_infinite(EN_NUMERAL));
    ext_numeral_kind ak;
    ak = EN_MINUS_INFINITY;
    reset(m, a, ak);
    ENSURE(is_zero(m, a, EN_NUMERAL));
    {
        std::ostringstream buffer;        
        display(buffer, m, a, ak); 
        ENSURE(buffer.str() == "0");
    }
    {
        std::ostringstream buffer;        
        m.set(a, -10);
        display(buffer, m, a, ak); 
        ENSURE(buffer.str() == "-10");
    }
    {
        std::ostringstream buffer;        
        display(buffer, m, a, EN_PLUS_INFINITY); 
        ENSURE(buffer.str() == "+oo");
    }
    {
        std::ostringstream buffer;        
        display(buffer, m, a, EN_MINUS_INFINITY); 
        ENSURE(buffer.str() == "-oo");
    }
}

void tst_ext_numeral() {
    tst1();
    tst2();
    tst3();
}
