/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpz.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-18.

Revision History:

--*/

#include "util/mpz.h"
#include "util/rational.h"
#include "util/timeit.h"
#include "util/scoped_numeral.h"

static void tst1() {
    synch_mpz_manager m;
    char const * str = "1002034040050606089383838288182";
    mpz v;
    m.set(v, str);
    std::cout << str << "\n" << m.to_string(v) << "\n";
    mpz v2, v3;
    m.mul(v, m.mk_z(-2), v2);
    std::cout << "*-2 = \n" << m.to_string(v2) << "\n";
    m.add(v, v2, v3);
    m.neg(v3);
    ENSURE(m.eq(v, v3));
    ENSURE(m.le(v, v3));
    ENSURE(m.ge(v, v3));
    ENSURE(m.lt(v2, v));
    ENSURE(m.le(v2, v));
    ENSURE(m.gt(v, v2));
    ENSURE(m.ge(v, v2));
    ENSURE(m.neq(v, v2));
    ENSURE(!m.neq(v, v3));
    m.del(v);
    m.del(v2);
    m.del(v3);
}

static void tst2() {
    synch_mpz_manager m;
    mpz v1, v2, v3;
    m.set(v1, static_cast<int64_t>(UINT_MAX));
    m.add(v1, m.mk_z(1), v2);
    m.mul(v2, v2, v3);
    std::cout << "v2:\n" << m.to_string(v2) << "\n";
    std::cout << "v2*v2:\n" << m.to_string(v3) << "\n";
    m.del(v1);
    m.del(v2);
    m.del(v3);
}

static void tst2b() {
    synch_mpz_manager m;
    mpz v1, v2, v3;
    m.set(v1, static_cast<int64_t>(UINT_MAX));
    m.add(v1, m.mk_z(1), v2);
    m.mul(v2, v2, v3);
    std::cout << "v2:\n" << m.to_string(v2) << "\n";
    std::cout << "v2*v2:\n" << m.to_string(v3) << "\n";
    m.mul(v2, v2, v2);
    m.mul(v2, v2, v2);
    m.mul(v2, v2, v2);
    std::cout << "v2: " << m.to_string(v2) << "\n";
    m.del(v1);
    m.del(v2);
    m.del(v3);
}

#if 0
static void mk_random_num_str(unsigned buffer_sz, char * buffer) {
    unsigned sz = (rand() % (buffer_sz-2)) + 1;
    ENSURE(sz < buffer_sz);
    for (unsigned i = 0; i < sz-1; i++) {
        buffer[i] = '0' + (rand() % 10);
    }
    if (rand() % 2 == 0)
        buffer[0] = '-';
    buffer[sz-1] = 0;
}
#endif

static void bug1() {
    synch_mpz_manager m;
    mpz v1;
    m.set(v1, "1002043949858757875676767675747473");
    mpz v2;
    m.sub(v1, v1, v2);
    ENSURE(m.is_zero(v2));
    m.del(v1);
    m.del(v2);
}

static void bug2() {
    synch_mpz_manager m;
    mpz v1, v2, vout;
    m.set(v1, "78160958900072552148646898355155840547214990303507678364419557473408815232466629049311995556059463490539128818602490221544425042127795");
    m.set(v2, "403412298227858394469856607272647132163832860126054679347881638761723785858733108109249157334220127");
    m.sub(v1, v2, vout);
    m.del(v1);
    m.del(v2);
    m.del(vout);
}

static void bug3() {
    synch_mpz_manager m;
    mpz v1, v2;
    m.set(v1, INT_MIN);
    m.set(v2, INT_MAX);
    m.add(v2, m.mk_z(1), v2);
    m.neg(v1);
    ENSURE(m.eq(v1, v2));
    m.del(v1);
    m.del(v2);
}

static void bug4() {
    synch_mpz_manager m;
    mpz x, y;
    m.set(y, static_cast<uint64_t>(4294967295ull));
    m.set(x, static_cast<uint64_t>(4026531839ull));
    mpz result1;
    m.bitwise_or(x, y, result1);

    mpz result2;
    m.set(result2, x);
    m.bitwise_or(result2, y, result2);
    
    std::cout << m.to_string(result1) << " " << m.to_string(result2) << "\n";
    ENSURE(m.eq(result1, result2));
    m.del(x); m.del(y); m.del(result1); m.del(result2);
}

void tst_div2k(synch_mpz_manager & m, mpz const & v, unsigned k) {
    mpz x, y, two(2), pw;
    m.machine_div2k(v, k, x);
    m.power(two, k, pw);
    m.machine_div(v, pw, y);
    bool is_eq = m.eq(x, y);
    (void)is_eq;
    CTRACE("mpz_2k", !is_eq, tout << "div: " << m.to_string(v) << ", k: " << k << " r: " << m.to_string(x) << ", expected: " << m.to_string(y) << "\n";);
    ENSURE(is_eq);
    m.del(x);
    m.del(y);
    m.del(pw);
}

void tst_div2k(synch_mpz_manager & m, int v, unsigned k) {
    mpz x;
    m.set(x, v);
    tst_div2k(m, x, k);
    m.del(x);
}

void tst_div2k(synch_mpz_manager & m, char const * v, unsigned k) {
    mpz x;
    m.set(x, v);
    tst_div2k(m, x, k);
    m.del(x);
}

void tst_mul2k(synch_mpz_manager & m, mpz const & v, unsigned k) {
    mpz x, y, two(2), pw;
    m.mul2k(v, k, x);
    m.power(two, k, pw);
    m.mul(v, pw, y);
    bool is_eq = m.eq(x, y);
    (void)is_eq;
    CTRACE("mpz_2k", !is_eq, tout << "mul: " << m.to_string(v) << ", k: " << k << " r: " << m.to_string(x) << ", expected: " << m.to_string(y) << "\n";);
    ENSURE(is_eq);
    m.del(x);
    m.del(y);
    m.del(pw);
}

void tst_mul2k(synch_mpz_manager & m, int v, unsigned k) {
    mpz x;
    m.set(x, v);
    tst_mul2k(m, x, k);
    m.del(x);
}

void tst_mul2k(synch_mpz_manager & m, char const * v, unsigned k) {
    mpz x;
    m.set(x, v);
    tst_mul2k(m, x, k);
    m.del(x);
}

static void tst_2k() {
    synch_mpz_manager m;
    tst_mul2k(m, 120, 32);
    tst_mul2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 22);
    tst_div2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 22);

    tst_div2k(m, 3, 1);
    tst_div2k(m, 3, 2);
    tst_div2k(m, 3, 0);
    tst_div2k(m, 120, 32);
    tst_div2k(m, 120, 0);
    tst_div2k(m, 81, 2);
    tst_div2k(m, -3, 1);
    tst_div2k(m, -3, 2);
    tst_div2k(m, -3, 0);
    tst_div2k(m, -102, 4);
    tst_div2k(m, 0, 3);
    tst_div2k(m, 0, 1000);
    tst_div2k(m, 7, 10000);
    tst_div2k(m, -7, 1000);
    tst_div2k(m, -7, 2);
    tst_div2k(m, "1029384848584832828327176162636436484", 4);
    tst_div2k(m, "1029384848584832828327176162636436484", 100);
    tst_div2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 1);
    tst_div2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 0);
    tst_div2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 4);
    tst_div2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 7);
    tst_div2k(m, "102938484858483282832717616263643648433838737661626264364583983298239291919", 100);
    tst_div2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 100);
    tst_div2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 177);
    tst_div2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 77);
    tst_div2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 32);
    tst_div2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 64);
    tst_div2k(m, "-11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 64);
    tst_div2k(m, "-11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 128);
    tst_div2k(m, "-1092983874757371817626399990000000", 100);
    tst_div2k(m, "-109298387475737181762639999000000231", 8);
    tst_div2k(m, "-109298387475737181762639999000000231", 16);
    tst_div2k(m, "-109298387475737181762639999000000231", 17);
    tst_div2k(m, "-109298387475737181762639999000000231", 32);


    tst_mul2k(m, 3, 1);
    tst_mul2k(m, 3, 2);
    tst_mul2k(m, 3, 0);
    tst_mul2k(m, 120, 32);
    tst_mul2k(m, 120, 0);
    tst_mul2k(m, 81, 2);
    tst_mul2k(m, -3, 1);
    tst_mul2k(m, -3, 2);
    tst_mul2k(m, -3, 0);
    tst_mul2k(m, -102, 4);
    tst_mul2k(m, 0, 3);
    tst_mul2k(m, 0, 1000);
    tst_mul2k(m, 7, 10000);
    tst_mul2k(m, -7, 1000000);
    tst_mul2k(m, -7, 2);
    tst_mul2k(m, "1029384848584832828327176162636436484", 4);
    tst_mul2k(m, "1029384848584832828327176162636436484", 100);
    tst_mul2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 1);
    tst_mul2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 0);
    tst_mul2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 4);
    tst_mul2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 22);
    tst_mul2k(m, "102938484858483282832717616263643648481827437292943727163646457588332211", 7);
    tst_mul2k(m, "102938484858483282832717616263643648433838737661626264364583983298239291919", 100);
    tst_mul2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 100);
    tst_mul2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 177);
    tst_mul2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 77);
    tst_mul2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 32);
    tst_mul2k(m, "11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 64);
    tst_mul2k(m, "-11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 64);
    tst_mul2k(m, "-11579208923731619542357098500868790785326998466564056403945758400793872761761638458372762", 128);
    tst_mul2k(m, "-1092983874757371817626399990000000", 100);
    tst_mul2k(m, "-109298387475737181762639999000000231", 8);
    tst_mul2k(m, "-109298387475737181762639999000000231", 16);
    tst_mul2k(m, "-109298387475737181762639999000000231", 17);
    tst_mul2k(m, "-109298387475737181762639999000000231", 32);
}

void tst_int_min_bug() {
    synch_mpz_manager m;
    mpz intmin(INT_MIN);
    mpz big;
    mpz expected;
    mpz r;
    m.set(big, static_cast<uint64_t>(UINT64_MAX));
    m.set(expected, "18446744075857035263");
    m.sub(big, intmin, r);
    std::cout << "r: " << m.to_string(r) << "\nexpected: " << m.to_string(expected) << "\n";
    ENSURE(m.eq(r, expected));
    m.del(intmin);
    m.del(big);
    m.del(expected);
    m.del(r);
}

void tst_scoped() {
    synch_mpz_manager m;
    scoped_synch_mpz a(m);
    scoped_synch_mpz b(m);
    m.set(a, 1000231);
    m.set(b, "102928187172727273");
    std::cout << "a: " << m.to_string(a) << "\n";
    std::cout << "b: " << m.to_string(b) << "\n";
    m.mul(a, b, b);
    std::cout << "b: " << m.to_string(b) << "\n";
}

#define NUM_PRIMES 168
unsigned g_primes[NUM_PRIMES] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997 };

// Return a big number by multipling powers of the first NUM_PRIMES.
// - ratio:  rand() % ratio == 0 is used to decide whether a specific prime will be included or not.
// - max_pw: if condition above is satisfied, then we use (rand() % max_pw) + 1 as the power.
void mk_big_num(unsynch_mpz_manager & m, unsigned ratio, unsigned max_pw, mpz & r) {
    scoped_mpz tmp(m);
    m.set(r, 1);
    for (unsigned i = 0; i < NUM_PRIMES; i++) {
        if ((rand() % ratio) == 0) {
            m.power(mpz(g_primes[i]), (rand() % max_pw) + 1, tmp);
            m.mul(r, tmp, r);
        }
    }
    if ((rand() % 2) == 0)
        m.neg(r);
}

void slow_gcd(unsynch_mpz_manager & m, mpz const & a, mpz const & b, mpz & c) {
    scoped_mpz tmp1(m);
    scoped_mpz tmp2(m);
    scoped_mpz aux(m);
    m.set(tmp1, a);
    m.set(tmp2, b);
    m.abs(tmp1);
    m.abs(tmp2);
    if (m.le(tmp1, tmp2))
        m.swap(tmp1, tmp2);
    if (m.is_zero(tmp2)) {
        m.set(c, tmp1);
        return;
    }
    for(;;) {
        m.rem(tmp1, tmp2, aux);
        if (m.is_zero(aux)) {
            m.set(c, tmp2);
            return;
        }
        m.set(tmp1, tmp2);
        m.set(tmp2, aux);
    }
}

void rand_tst_gcd(unsigned num, unsigned ratio, unsigned pw) {
    unsynch_mpz_manager m;
    scoped_mpz a(m);
    scoped_mpz b(m);
    scoped_mpz g1(m);
    scoped_mpz g2(m);

    for (unsigned i = 0; i < num; i++) {
        mk_big_num(m, ratio, pw, a);
        mk_big_num(m, ratio, pw, b);
        slow_gcd(m, a, b, g1);
        m.gcd(a, b, g2);
        std::cout << "a:  " << m.to_string(a) << "\n";
        std::cout << "b:  " << m.to_string(b) << "\n";
        std::cout << "g1: " << m.to_string(g1) << "\n";
        std::cout << "g2: " << m.to_string(g2) << "\n";
        std::cout << "\n";
        if (!m.eq(g1, g2)) {
            std::cout << "\n\nBUG\n\n";
            UNREACHABLE();
        }
    }
}

void tst_gcd() {
    unsynch_mpz_manager m;
    scoped_mpz a(m);
    scoped_mpz b(m);
    scoped_mpz g(m);
    m.set(a, "125141154046000416200229049397707776");
    m.set(b, "67062117506072642958648904906464");
    m.gcd(a, b, g);
    std::cout << "g: " << m.to_string(g) << "\n";
    m.set(a, "664877781119188360263909568610284290708591605105963082581413244598320881431041311468785283029437655134762231312337924555674674176");
    m.set(b, "21691055098083293041646678174999125628463716392747356050705870375852789453851926624107939885328471215366825649627326658281728580399051770334114658498352848410853519374962852431831492868108719406669605254329669417322836882756478295264");
    for (unsigned i = 0; i < 50000; i++) {
        m.del(g);
        m.gcd(a, b, g);
        // slow_gcd(m, a, b, g);
    }
    std::cout << "g: " << m.to_string(g) << "\n";
}

void tst_log2(unsynch_mpz_manager & m, mpz const & a) {
    scoped_mpz b(m);
    unsigned k = m.log2(a);
    m.power(mpz(2), k, b);
    ENSURE(m.is_zero(a) || m.le(b, a));
    m.power(mpz(2), k+1, b);
    ENSURE(m.le(a, b));

    scoped_mpz neg_a(m);
    m.set(neg_a, a);
    m.neg(neg_a);
    k = m.mlog2(neg_a);
    m.power(mpz(2), k, b);
    m.neg(b);
    ENSURE(m.is_zero(neg_a) || m.le(neg_a, b));
    m.power(mpz(2), k+1, b);
    m.neg(b);
    ENSURE(m.le(b, neg_a));
}

void tst_log2() {
    unsynch_mpz_manager m;
    for (unsigned i = 0; i <= 64; i++)
        std::cout << "log2(" << i << "): " << m.log2(mpz(i)) << "\n";
    for (unsigned i = 0; i < 1000; i++)
        tst_log2(m, mpz(i));
    scoped_mpz a(m);
    m.set(a, "1029489380487098723984579237");
    for (unsigned i = 0; i < 1000; i++) {
        m.inc(a);
        tst_log2(m, a);
    }
}

void tst_root() {
    unsynch_mpz_manager m;
    scoped_mpz a(m);
    m.set(a, 213);
    VERIFY(!m.root(a, 5));
    std::cout << "213^{1/5}: " << a << "\n";
    ENSURE(m.eq(a, mpz(3)));
    m.set(a, -213);
    VERIFY(!m.root(a, 5));
    std::cout << "-213^{1/5}: " << a << "\n";
    ENSURE(m.eq(a, mpz(-2)));
    m.set(a, 0);
    VERIFY(m.root(a, 3));
    ENSURE(m.is_zero(a));
    m.set(a, 8);
    VERIFY(m.root(a, 3));
    ENSURE(m.eq(a, mpz(2)));
    m.set(a, -8);
    VERIFY(m.root(a, 3));
    ENSURE(m.eq(a, mpz(-2)));
}

void tst_gcd_bug() {
    unsynch_mpz_manager m;
    scoped_mpz a(m), b(m), g(m);
    m.set(a, INT_MIN);
    m.set(b, INT_MIN);
    m.gcd(a, b, g);
    std::cout << "g: " << g << "\n";
}

void tst_div2k_bug() {
    unsynch_mpz_manager m;
    scoped_mpz a(m), b(m), g(m);
    m.set(a, UINT_MAX);
    m.machine_div2k(a, 32, b);
    std::cout << "a: " << a << ", b: " << b << "\n";
}


static void tst5() {
    unsynch_mpz_manager m;
    scoped_mpz a(m);
    a = 1;
    std::cout << "1 -> " << m.log2(a) << "\n";
    a = 5;
    std::cout << "5 -> " << m.log2(a) << "\n";
    a = 16;
    std::cout << "16 -> " << m.log2(a) << "\n";
    a = INT_MAX;
    std::cout << "INT_MAX -> " << m.log2(a) << "\n";
    a = INT_MAX/4;
    std::cout << "INT_MAX/4 -> " << m.log2(a) << "\n";
}

static void tst_pw2() {
    unsynch_mpz_manager m;
    scoped_mpz a(m);
    for (unsigned i = 0; i < 128; i++) {
        m.power(mpz(2), i, a);
        std::cout << "i: " << i << ", a: " << a << std::endl;
    }
}

void tst_mpz() {
    disable_trace("mpz");
    enable_trace("mpz_2k");
    tst_pw2();
    tst5();
    tst_div2k_bug();
    rand_tst_gcd(50, 3, 2);
    tst_2k();
    tst_gcd_bug();
    tst_root();
    tst_log2();
    // tst_gcd();
    tst_scoped();
    tst_int_min_bug();
    bug4();
    bug3();
    bug1();
    bug2();
    tst1();
    tst2();
    tst2b();
}
