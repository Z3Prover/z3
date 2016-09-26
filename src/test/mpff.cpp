/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpff.cpp

Abstract:

    mpff tests...

Author:

    Leonardo de Moura (leonardo) 2012-09-12.

Revision History:

--*/
#include<sstream>
#include"mpff.h"
#include"mpz.h"
#include"mpq.h"

static void tst1() {
    try {
        mpff_manager m;
        // m.round_to_minus_inf();
        scoped_mpff  a(m), b(m);
        m.set(a, 100);
        m.set(b, -33);
        std::cout << "a: " << a << ", b: " << b << "\n";
        std::cout << "a*b: " << a*b << "\n";
        for (unsigned i = 0; i < 100; i++) {
            a = a*a;
            std::cout << i << ": " << a << "\n";
        }
    }
    catch (z3_exception & ex) {
        std::cout << ex.msg() << "\n";
    }
}

static void tst2() {
    mpff_manager m;
    scoped_mpff a(m), b(m);
    m.set(a, static_cast<uint64>(100));
    m.set(b, static_cast<int64>(-100));
    std::cout << "[test2], a: " << a << ", b: " << b << "\n";
}

static void tst3() {
    mpff_manager m;
    scoped_mpff a(m), b(m), c(m);
    m.set(a, 1);
    m.set(b, 3);
    m.div(a, b, c);
    std::cout << "[div] c: " << c << "\n";
    m.round_to_plus_inf();
    m.reset(c);
    m.div(a, b, c);
    std::cout << "[div] c: " << c << "\n";
}

static void tst4() {
    unsynch_mpz_manager zm;
    mpff_manager m;
    scoped_mpz a(zm);
    scoped_mpff b(m);
    zm.set(a, 2);
    zm.power(a, 512, a);
    m.set(b, zm, a);
    std::cout << "[mpz->mpff] a: " << a << ", b: " << b << "\n";
}

static void tst5() {
    mpff_manager m;
    scoped_mpff a(m), b(m);
    m.set(a, static_cast<uint64>(1) << 63);
    m.display_raw(std::cout, a); std::cout << "\n";
    SASSERT(m.is_zero(b));
    SASSERT(m.lt(b, a));
    m.set(b, -1);
    SASSERT(m.lt(b, a));
}

static void tst6() {
    mpff_manager m;
    scoped_mpff a(m), b(m), one(m);
    m.set(a, 1, 3);
    std::cout << "mpff(1/3) " << a << "\n";
    b = a;
    m.next(b);
    SASSERT(m.lt(a, b));
    std::cout << "b: " << b << "\n";
    m.prev(b);
    SASSERT(m.eq(a, b));
    m.ceil(b);
    std::cout << "b: " << b << "\n";
    m.set(b, 4, 3);
    std::cout << "b: " << b << "\n";
    m.ceil(b);
    std::cout << "b: " << b << "\n";
}

static void tst7() {
    mpff_manager m;
    scoped_mpff a(m);
    m.set(a, 2);
    m.display_smt2(std::cout, a); std::cout << "\n";
    m.set(a, -2);
    m.display_smt2(std::cout, a); std::cout << "\n";
    m.set(a, 1, 3);
    m.display_smt2(std::cout, a); std::cout << "\n";
}

//  if (!qm.le(qa, qt)) { TRACE("mpff_bug", tout << fa << "\n" << qa << "\n" << qt << "\n";); UNREACHABLE(); }


#define MK_BIN_OP(OP)                                                   \
static void tst_ ## OP ## _core(int64 n1, uint64 d1, int64 n2, uint64 d2, unsigned precision = 2, unsigned exp = 0) { \
    TRACE("mpff_bug", tout << n1 << "/" << d1 << ", " << n2 << "/" << d2 << "\n";); \
    unsynch_mpq_manager qm;                                             \
    scoped_mpq  qa(qm), qb(qm), qc(qm), qt(qm);                         \
                                                                        \
    mpff_manager        fm(precision);                                  \
    scoped_mpff fa(fm), fb(fm), fc1(fm), fc2(fm);                       \
    fm.set(fa, n1, d1);                                                 \
    if (exp != 0) { int _exp = rand() % exp; if (rand() % 2 == 0) _exp = -_exp; fm.set_exponent(fa, _exp); } \
    fm.to_mpq(fa, qm, qa);                                              \
    fm.set(fb, n2, d2);                                                 \
    if (exp != 0) { int _exp = rand() % exp; if (rand() % 2 == 0) _exp = -_exp; fm.set_exponent(fb, _exp); } \
    fm.to_mpq(fb, qm, qb);                                              \
    qm.OP(qa, qb, qc);                                                  \
    {                                                                   \
        fm.round_to_plus_inf();                                         \
        fm.OP(fa, fb, fc1);                                             \
        fm.to_mpq(fc1, qm, qt);                                         \
        SASSERT(qm.le(qc, qt));                                         \
    }                                                                   \
    {                                                                   \
        fm.round_to_minus_inf();                                        \
        fm.OP(fa, fb, fc2);                                             \
        fm.to_mpq(fc2, qm, qt);                                         \
        SASSERT(qm.le(qt, qc));                                         \
    }                                                                   \
    SASSERT(fm.le(fc2, fc1));                                           \
}

MK_BIN_OP(add);
MK_BIN_OP(sub);
MK_BIN_OP(mul);
MK_BIN_OP(div);

#define MK_BIN_RANDOM_TST(OP)                                           \
    static void tst_ ## OP(unsigned N, unsigned max, unsigned prec = 2, bool is_div = false) { \
    for (unsigned i = 0; i < N; i++) {                                  \
        int n1 = rand() % max;                                          \
        int d1 = rand() % max + 1;                                      \
        int n2 = rand() % max;                                          \
        int d2 = rand() % max + 1;                                      \
        if (rand () % 2 == 0)                                           \
            n1 = -n1;                                                   \
        if (rand () % 2 == 0)                                           \
            n2 = -n2;                                                   \
        if (is_div && n2 == 0) n2 = 1;                                  \
        tst_ ## OP ## _core(n1, d1, n2, d2, prec);                      \
        tst_ ## OP ## _core(n1, d1, n2, d2, prec, 512);                 \
    }                                                                   \
}

MK_BIN_RANDOM_TST(add)
MK_BIN_RANDOM_TST(sub)
MK_BIN_RANDOM_TST(mul)
MK_BIN_RANDOM_TST(div)

static void tst_bug() {
    unsynch_mpq_manager qm;
    mpff_manager fm;
    fm.round_to_plus_inf();
    scoped_mpff a(fm);
    fm.set(a, 41, 36);
    scoped_mpq  b(qm), c(qm);
    qm.set(b, 41, 36);
    fm.to_mpq(a, qm, c);
    SASSERT(qm.le(b, c));
}

static void tst_bug2() {
    mpff_manager fm(4);
    scoped_mpff a(fm), b(fm);
    fm.set(b, 1);
    fm.sub(a, b, b);
    fm.set(a, -1);
    SASSERT(fm.eq(a, b));
    fm.set(a, 1);
    fm.set(b, 0);
    fm.sub(a, b, a);
    fm.set(b, 1);
    SASSERT(fm.eq(a, b));
    fm.set(a, 1);
    fm.set(b, 1);
    fm.sub(a, b, a);
    SASSERT(fm.is_zero(a));
}

static void tst_set64(unsigned N, unsigned prec) {
    mpff_manager fm(prec);
    scoped_mpff a(fm);

    fm.set(a, static_cast<int64>(INT64_MAX));
    SASSERT(fm.is_int64(a));
    SASSERT(fm.is_uint64(a));
    fm.inc(a);
    SASSERT(!fm.is_int64(a));
    SASSERT(fm.is_uint64(a));
    SASSERT(fm.is_int(a));
    fm.dec(a);
    SASSERT(fm.is_int64(a));
    SASSERT(fm.is_uint64(a));
    fm.dec(a);
    SASSERT(fm.is_int64(a));
    SASSERT(fm.is_uint64(a));

    fm.set(a, static_cast<int64>(INT64_MIN));
    SASSERT(fm.is_int64(a));
    SASSERT(!fm.is_uint64(a));
    fm.dec(a);
    SASSERT(!fm.is_int64(a));
    SASSERT(!fm.is_uint64(a));
    SASSERT(fm.is_int(a));
    fm.inc(a);
    SASSERT(fm.is_int64(a));
    SASSERT(!fm.is_uint64(a));
    fm.inc(a);
    SASSERT(fm.is_int64(a));
    SASSERT(!fm.is_uint64(a));

    fm.set(a, static_cast<uint64>(UINT64_MAX));
    SASSERT(fm.is_uint64(a));
    SASSERT(!fm.is_int64(a));
    fm.inc(a);
    SASSERT(!fm.is_uint64(a));
    SASSERT(!fm.is_int64(a));
    fm.dec(a);
    SASSERT(fm.is_uint64(a));
    SASSERT(!fm.is_int64(a));
    fm.dec(a);
    SASSERT(fm.is_uint64(a));
    SASSERT(!fm.is_int64(a));

    for (unsigned i = 0; i < N; i++) {
        {
            uint64 v = (static_cast<uint64>(rand()) << 32) + static_cast<uint64>(rand()); 
            fm.set(a, v);
            SASSERT(fm.is_uint64(a));
            
            v = (static_cast<uint64>(rand() % 3) << 32) + static_cast<uint64>(rand()); 
            fm.set(a, v);
            SASSERT(fm.is_uint64(a));
        }
        {
            int64 v = (static_cast<uint64>(rand() % INT_MAX) << 32) + static_cast<uint64>(rand());
            if (rand()%2 == 0)
                v = -v;
            fm.set(a, v);
            SASSERT(fm.is_int64(a));


            v = (static_cast<uint64>(rand() % 3) << 32) + static_cast<uint64>(rand());
            if (rand()%2 == 0)
                v = -v;
            fm.set(a, v);
            SASSERT(fm.is_int64(a));
        }
    }
}

static void tst_capacity(unsigned prec = 2) {
    mpff_manager m(prec);
    scoped_mpff_vector v(m);
    scoped_mpff a(m);
    for (unsigned i = 0; i < 50000; i++) {
        m.set(a, i);
        v.push_back(a);
        SASSERT(m.is_int(v.back()));
        SASSERT(m.is_int64(v.back()));
        SASSERT(m.is_uint64(v.back()));
    }
    for (unsigned i = 0; i < 50000; i++) {
        SASSERT(m.get_int64(v[i]) == i);
    }
}

static void tst_power(unsigned prec = 2) {
    mpff_manager m(prec);
    scoped_mpff a(m), b(m);

    // 0^k == 0
    SASSERT(m.is_zero(a));
    m.power(a, 10, a);
    SASSERT(m.is_zero(a));

    // a != 0 ==> a^0 == 1
    m.set(a, 33);
    m.power(a, 0, a);
    SASSERT(m.is_one(a));
    m.set(a, -33);
    m.power(a, 0, a);
    SASSERT(m.is_one(a));
    
    // a^1 == a
    m.set(a, 33);
    m.power(a, 1, b);
    SASSERT(m.eq(a, b));
    m.set(a, -33);
    m.power(a, 1, b);
    SASSERT(m.eq(a, b));

    // checking special support for powers of 2 
#ifdef Z3DEBUG
    unsigned k;
#endif
    m.set(a, 1);
    SASSERT(m.is_power_of_two(a, k) && k == 0);
    m.set(a, 2);
    SASSERT(m.is_power_of_two(a, k) && k == 1);
    m.set(a, 3);
    SASSERT(!m.is_power_of_two(a, k));
    m.set(a, 4);
    SASSERT(m.is_power_of_two(a, k) && k == 2);
    m.set(a, -4);
    SASSERT(!m.is_power_of_two(a, k));
    m.set(a, 8);
    SASSERT(m.is_power_of_two(a, k) && k == 3);
    m.set(a, 0);
    SASSERT(!m.is_power_of_two(a));

    m.set(a, UINT_MAX);
    m.inc(a);
    SASSERT(m.is_power_of_two(a, k) && k == 32);
    SASSERT(m.get_uint64(a) == static_cast<uint64>(UINT_MAX) + 1);
    m.power(a, 2, a);
    SASSERT(m.is_power_of_two(a, k) && k == 64);
    m.power(a, 4, a);
    SASSERT(m.is_power_of_two(a, k) && k == 256);
    m.round_to_plus_inf();
    m.inc(a);
    SASSERT(!m.is_power_of_two(a, k));

    m.set(a, -4);
    m.power(a, 3, a);
    m.set(b, -64);
    SASSERT(m.eq(a, b));
    m.set(a, -4);
    m.power(a, 4, a);
    m.set(b, 256);
    SASSERT(m.eq(a, b));

    // additional tests
    m.set(a, 5);
    m.power(a, 3, a);
    m.set(b, 5*5*5);
    SASSERT(m.eq(a,b));
    
    m.set(a, -5);
    m.power(a, 3, a);
    m.set(b, -5*5*5);
    SASSERT(m.eq(a,b));
}

static void tst_sgn(unsigned prec) {
    mpff_manager m(prec);
    scoped_mpff a(m), b(m);
    SASSERT(m.is_zero(a) && !m.is_pos(a) && !m.is_neg(a) && m.is_nonpos(a) && m.is_nonneg(a));
    m.set(a, 3);
    SASSERT(!m.is_zero(a) && m.is_pos(a) && !m.is_neg(a) && !m.is_nonpos(a) && m.is_nonneg(a));
    m.set(a, -3);
    SASSERT(!m.is_zero(a) && !m.is_pos(a) && m.is_neg(a) && m.is_nonpos(a) && !m.is_nonneg(a));
    m.set(a, 8);
    m.power(a, 256, a);
    SASSERT(!m.is_zero(a) && m.is_pos(a) && !m.is_neg(a) && !m.is_nonpos(a) && m.is_nonneg(a));
    b = a;
    m.neg(a);
    SASSERT(m.neq(a, b));
    SASSERT(!m.is_zero(a) && !m.is_pos(a) && m.is_neg(a) && m.is_nonpos(a) && !m.is_nonneg(a));
    m.neg(a);
    SASSERT(m.eq(a, b));


    m.set(a, 1);
    SASSERT(m.is_one(a) && !m.is_zero(a) && !m.is_minus_one(a) && m.is_abs_one(a));
    m.neg(a);
    SASSERT(!m.is_one(a) && !m.is_zero(a) && m.is_minus_one(a) && m.is_abs_one(a));
    m.set(a, 3);
    SASSERT(!m.is_one(a) && !m.is_zero(a) && !m.is_minus_one(a));

    m.set(a, 3);
    b = a;
    m.abs(a);
    SASSERT(m.eq(a, b));
    m.set(a, -3);
    b = a;
    m.abs(a);
    SASSERT(!m.eq(a,b) && m.is_pos(a));

    m.set(a, 1);
    m.swap(a, a);
    SASSERT(m.is_one(a));
    m.set(b, -1);
    m.swap(a, b);
    SASSERT(m.is_one(b) && m.is_minus_one(a));
    m.neg(a);
    SASSERT(m.eq(a, b));
}

static void tst_limits(unsigned prec) {
    mpff_manager m(prec);
    scoped_mpff a(m), b(m), two(m);
    m.set_max(a);
    SASSERT(m.is_pos(a));
    m.set_min(b);
    SASSERT(m.is_neg(b));
    m.neg(a);
    SASSERT(m.eq(a, b));

    m.set_max(a);
    m.set_max(b);
    m.round_to_minus_inf();
    m.inc(a);
    SASSERT(m.eq(a, b));
    m.dec(a);
    SASSERT(m.lt(a, b));
    m.set_max(a);
    m.round_to_plus_inf();
    bool overflow = false;
    try { m.inc(a); }
    catch (mpff_manager::overflow_exception) { overflow = true; }
    SASSERT(overflow);
    m.set_max(a);
    m.dec(a);
    SASSERT(m.eq(a, b));
    
    
    m.set_min(a);
    m.set_min(b);
    m.round_to_minus_inf();
    m.inc(a);
    SASSERT(m.eq(a, b));
    overflow = true;
    try { m.dec(a); }
    catch (mpff_manager::overflow_exception) { overflow = true; }
    SASSERT(overflow);
    m.round_to_plus_inf();
    m.set_min(a);
    m.inc(a);
    SASSERT(m.gt(a,b));
    m.set_min(a);
    m.dec(a);
    SASSERT(m.eq(a,b));

    m.set_plus_epsilon(a);
    m.set_plus_epsilon(b);
    SASSERT(!m.is_zero(a) && m.is_pos(a));
    m.set(two, 2);
    m.round_to_plus_inf();
    m.div(a, two, a);
    SASSERT(m.eq(a, b));
    m.round_to_minus_inf();
    m.div(a, two, a);
    SASSERT(m.is_zero(a));
    m.round_to_plus_inf();
    m.set_plus_epsilon(a);
    m.add(a, a, a);
    SASSERT(m.gt(a, b));
    m.round_to_minus_inf();
    m.set_plus_epsilon(a);
    m.add(a, a, a);
    SASSERT(m.gt(a, b));
    m.set_plus_epsilon(a);
    m.sub(a, a, a);
    SASSERT(m.is_zero(a));
    m.set_plus_epsilon(a);
    SASSERT(m.is_plus_epsilon(a));
    SASSERT(!m.is_minus_epsilon(a));
    m.neg(a);
    SASSERT(!m.is_plus_epsilon(a));
    SASSERT(m.is_minus_epsilon(a));
    
    for (unsigned i = 0; i < 2; i++) {
        m.set_rounding(i == 0);
        
        m.set_plus_epsilon(a);
        m.floor(a);
        SASSERT(m.is_zero(a));
        m.set_plus_epsilon(a);
        m.ceil(a);
        SASSERT(m.is_one(a));
        
        m.set_minus_epsilon(a);
        m.floor(a);
        SASSERT(m.is_minus_one(a));
        m.set_minus_epsilon(a);
        m.ceil(a);
        SASSERT(m.is_zero(a));
    }

    m.set_minus_epsilon(a);
    m.set_minus_epsilon(b);
    SASSERT(!m.is_zero(a) && m.is_neg(a));
    m.set(two, 2);
    m.round_to_minus_inf();
    m.div(a, two, a);
    SASSERT(m.eq(a, b));
    m.round_to_plus_inf();
    m.div(a, two, a);
    SASSERT(m.is_zero(a));
    m.round_to_plus_inf();
    m.set_minus_epsilon(a);
    m.add(a, a, a);
    SASSERT(m.lt(a, b));
    m.round_to_minus_inf();
    m.set_minus_epsilon(a);
    m.add(a, a, a);
    SASSERT(m.lt(a, b));
    m.set_minus_epsilon(a);
    m.sub(a, a, a);
    SASSERT(m.is_zero(a));
    m.set_minus_epsilon(a);
    SASSERT(!m.is_plus_epsilon(a));
    SASSERT(m.is_minus_epsilon(a));
    m.neg(a);
    SASSERT(m.is_plus_epsilon(a));
    SASSERT(!m.is_minus_epsilon(a));
}

#if 0
static void tst_add_corner(unsigned prec) {
    mpff_manager m(prec);
    scoped_mpff a(m), b(m);
}
#endif

static void tst_decimal(int64 n, uint64 d, bool to_plus_inf, unsigned prec, char const * expected, unsigned decimal_places = UINT_MAX) {
    mpff_manager m(prec);
    scoped_mpff a(m);
    m.set_rounding(to_plus_inf);
    m.set(a, n, d);
    m.display(std::cout, a); std::cout << std::endl;
    m.display_decimal(std::cout, a, decimal_places); std::cout << std::endl;
    std::ostringstream buffer;
    m.display_decimal(buffer, a, decimal_places);
    SASSERT(strcmp(expected, buffer.str().c_str()) == 0);
}

static void tst_decimal() {
    tst_decimal(1, 3, false, 2, "0.3333333333333333333152632971252415927665424533188343048095703125");
    tst_decimal(1, 3, false, 4, "0.33333333333333333333333333333333333333235375470764809374335938621898146193515111203602326039874270691143465228378772735595703125");
    tst_decimal(-1, 3, true, 2, "-0.3333333333333333333152632971252415927665424533188343048095703125");
    tst_decimal(-1, 3, false, 2, "-0.33333333333333333334236835143737920361672877334058284759521484375");
    tst_decimal(0, 1, false, 2,  "0");
    tst_decimal(2, 1, false, 2,  "2");    
    tst_decimal(-3, 1, false, 2,  "-3");
    tst_decimal(INT64_MAX, 1, false, 2, "9223372036854775807");
    tst_decimal(4, 5, false, 2, "0.79999999999999999995663191310057982263970188796520233154296875");
    tst_decimal(4, 5, false, 2, "0.7999999999?", 10);
    tst_decimal(32, 5, true, 2, "6.4000000000000000000867361737988403547205962240695953369140625");
    tst_decimal(32, 5, false, 2, "6.39999999999999999965305530480463858111761510372161865234375");
    tst_decimal(-32, 5, false, 2, "-6.4000000000000000000867361737988403547205962240695953369140625");
    tst_decimal(-32, 5, true, 2, "-6.39999999999999999965305530480463858111761510372161865234375");
}

static void tst_prev_power_2(int64 n, uint64 d, unsigned expected) {
    mpff_manager m;
    scoped_mpff a(m);
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

static void tst_div(unsigned prec) {
    mpff_manager m(prec);
    scoped_mpff a(m), b(m), c(m);
    m.round_to_plus_inf();
    m.set(a, 1);
    m.set(b, static_cast<uint64>(UINT64_MAX));
    m.div(a, b, c);
    m.display_raw(std::cout, a); std::cout << "\n";
    m.display_raw(std::cout, b); std::cout << "\n";
    std::cout << a << "/" << b << " <= " << c << "\n";
    // 10...0 0...0
    //        11111
}

void tst_mpff() {
    disable_trace("mpff");
    enable_trace("mpff_trace");
    // enable_trace("mpff_bug");
    // enable_trace("mpff_to_mpq");
    //
    tst_div(2);
    tst_prev_power_2();
    tst_decimal();
    tst_div_core(679, 396, 279, 756, 2, 0);
    tst_limits(2);
    tst_limits(4);
    tst_sgn(2);
    tst_sgn(4);
    tst_sgn(8);
    tst_power(2);
    tst_power(4);
    tst_power(18);
    tst_capacity(2);
    tst_capacity(4);
    tst_capacity(8);
    tst_capacity(16);
    tst_set64(1000, 2);
    tst_set64(1000, 4);
    tst_set64(1000, 6);
    tst_bug2();

    tst_sub(1000, 1024, 2);
    tst_sub(1000, 1024, 4);
    tst_div(1000, 1024, 2, true);
    tst_div(1000, 1024, 4, true);
    tst_mul(1000, 1024, 2);
    tst_mul(1000, 1024, 4);
    tst_add(1000, 1024, 2);
    tst_add(1000, 1024, 4);

    tst_sub(1000, UINT_MAX, 2);
    tst_sub(1000, UINT_MAX, 4);
    tst_div(1000, UINT_MAX, 2, true);
    tst_div(1000, UINT_MAX, 4, true);
    tst_mul(1000, UINT_MAX, 2);
    tst_mul(1000, UINT_MAX, 4);
    tst_add(1000, UINT_MAX, 2);
    tst_add(1000, UINT_MAX, 4);

    tst_bug2();
    tst_bug();
    tst_add_core(1,1, 1,1);
    tst_add_core(1,3, 2,3);
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
}
