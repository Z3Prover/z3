/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    checked_int64.cpp

Abstract:

    Test checked_int64 against exact rational arithmetic.

    With CHECK=true, every operation must either return the exact
    result or throw overflow_exception, and it must throw exactly when the
    exact result is not representable as an int64_t (or the divisor is 0).
    With CHECK=false, INT64_MIN / -1 and INT64_MIN % -1 must not trap.

--*/

#include "util/checked_int64.h"
#include "util/rational.h"
#include "util/debug.h"
#include "util/vector.h"
#include "util/util.h"
#include <iostream>

typedef checked_int64<true> ci64;
typedef checked_int64<false> ui64;

static unsigned s_failures = 0;

static rational r64(int64_t v) { return rational(v, rational::i64()); }

static void fail(char const* op, int64_t a, int64_t b, char const* msg) {
    ++s_failures;
    std::cout << "checked_int64 FAIL: " << op << "(" << a << ", " << b << "): " << msg << "\n";
}

// Run f; it must return exactly `expected` if `defined` holds and `expected`
// fits in int64, and must throw overflow_exception otherwise.
template<typename F>
static void check(char const* op, int64_t a, int64_t b, bool defined, rational const& expected, F f) {
    bool thrown = false;
    int64_t r = 0;
    try {
        r = f().get_int64();
    }
    catch (overflow_exception&) {
        thrown = true;
    }
    bool representable = defined && expected.is_int64();
    if (representable && thrown)
        fail(op, a, b, "unexpected overflow_exception");
    else if (representable && r != expected.get_int64())
        fail(op, a, b, "wrong result");
    else if (!representable && !thrown)
        fail(op, a, b, "missing overflow_exception");
}

static vector<int64_t> boundary_values() {
    int64_t const pos[] = {
        1, 2, 3, 4,
        (int64_t(1) << 31) - 1, int64_t(1) << 31, (int64_t(1) << 31) + 1,
        (int64_t(1) << 32) - 1, int64_t(1) << 32, (int64_t(1) << 32) + 1,
        3037000499, 3037000500,                     // floor/ceil of sqrt(2^63)
        (int64_t(1) << 62) - 1, int64_t(1) << 62, (int64_t(1) << 62) + 1,
        INT64_MAX / 3, INT64_MAX - 1, INT64_MAX
    };
    vector<int64_t> vs;
    vs.push_back(0);
    vs.push_back(INT64_MIN);
    for (int64_t v : pos) {
        vs.push_back(v);
        vs.push_back(-v);
    }
    return vs;
}

// Euclidean division: a = q*b + r with 0 <= r < |b|.
static rational euclid_mod(rational const& a, rational const& b) {
    rational r = a - machine_div(a, b) * b;
    if (r.is_neg())
        r += abs(b);
    return r;
}

static rational euclid_div(rational const& a, rational const& b) {
    return (a - euclid_mod(a, b)) / b;
}

static void tst_binary(int64_t a, int64_t b) {
    rational ra = r64(a), rb = r64(b);
    ci64 ca(a), cb(b);
    bool nz = b != 0;
    check("+", a, b, true, ra + rb, [&]() { return ca + cb; });
    check("-", a, b, true, ra - rb, [&]() { return ca - cb; });
    check("*", a, b, true, ra * rb, [&]() { return ca * cb; });
    check("/", a, b, nz, nz ? machine_div(ra, rb) : rational::zero(), [&]() { return ca / cb; });
    check("%", a, b, nz, nz ? ra - machine_div(ra, rb) * rb : rational::zero(), [&]() { ci64 r(ca); r %= cb; return r; });
    check("div", a, b, nz, nz ? euclid_div(ra, rb) : rational::zero(), [&]() { return div(ca, cb); });
    check("mod", a, b, nz, nz ? euclid_mod(ra, rb) : rational::zero(), [&]() { return mod(ca, cb); });

    // divides(a, b) is mod(b, a) == 0; it throws only for a == 0.
    if (a != 0) {
        try {
            if (divides(ca, cb) != euclid_mod(rb, ra).is_zero())
                fail("divides", a, b, "wrong result");
        }
        catch (overflow_exception&) {
            fail("divides", a, b, "unexpected overflow_exception");
        }
    }
    else {
        bool thrown = false;
        try {
            divides(ca, cb);
        }
        catch (overflow_exception&) {
            thrown = true;
        }
        if (!thrown)
            fail("divides", a, b, "missing overflow_exception");
    }

    // CHECK=false: where the exact result fits, division agrees with it.
    // INT64_MIN / -1 wraps to INT64_MIN and INT64_MIN % -1 is 0; neither traps.
    if (nz) {
        ui64 ua(a), ub(b);
        bool wraps = a == INT64_MIN && b == -1;
        int64_t q = wraps ? INT64_MIN : machine_div(ra, rb).get_int64();
        int64_t eq = wraps ? INT64_MIN : euclid_div(ra, rb).get_int64();
        ui64 ur(ua);
        ur %= ub;
        if ((ua / ub).get_int64() != q)
            fail("unchecked /", a, b, "wrong result");
        if (ur.get_int64() != (ra - machine_div(ra, rb) * rb).get_int64())
            fail("unchecked %", a, b, "wrong result");
        if (div(ua, ub).get_int64() != eq)
            fail("unchecked div", a, b, "wrong result");
        if (mod(ua, ub).get_int64() != euclid_mod(ra, rb).get_int64())
            fail("unchecked mod", a, b, "wrong result");
    }
}

static void tst_unary(int64_t a) {
    rational ra = r64(a);
    ci64 ca(a);
    check("neg", a, 0, true, -ra, [&]() { return -ca; });
    check("abs", a, 0, true, abs(ra), [&]() { return abs(ca); });
    check("++", a, 0, true, ra + rational::one(), [&]() { ci64 r(ca); return ++r; });
    check("--", a, 0, true, ra - rational::one(), [&]() { ci64 r(ca); return --r; });
    check("post++", a, 0, true, ra + rational::one(), [&]() { ci64 r(ca); r++; return r; });
    check("post--", a, 0, true, ra - rational::one(), [&]() { ci64 r(ca); r--; return r; });
    if (ca.is_even() != euclid_mod(ra, rational(2)).is_zero())
        fail("is_even", a, 0, "wrong result");
}

static void tst_gcd(int64_t a, int64_t b) {
    rational ra = r64(a), rb = r64(b);
    rational g = gcd(ra, rb);
    ci64 ca(a), cb(b);
    check("gcd", a, b, true, g, [&]() { return gcd(ca, cb); });

    // Extended gcd: a*x + b*y == gcd(a, b) >= 0; it throws only when the
    // gcd (2^63) is not representable.
    ci64 x, y;
    bool thrown = false;
    try {
        ci64 eg = gcd(ca, cb, x, y);
        if (eg.to_rational() != g)
            fail("extended gcd", a, b, "wrong gcd");
        else if (ra * x.to_rational() + rb * y.to_rational() != g)
            fail("extended gcd", a, b, "wrong Bezout coefficients");
    }
    catch (overflow_exception&) {
        thrown = true;
    }
    if (thrown && g.is_int64())
        fail("extended gcd", a, b, "unexpected overflow_exception");
    if (!thrown && !g.is_int64())
        fail("extended gcd", a, b, "missing overflow_exception");
}

// A value of random magnitude (0 to 63 bits) and sign.
static int64_t random_value(random_gen& rand) {
    uint64_t v = rand.next_uint64() >> (rand() % 64);
    return static_cast<int64_t>(rand() % 2 ? 0 - v : v);
}

void tst_checked_int64() {
    vector<int64_t> vs = boundary_values();
    for (int64_t a : vs) {
        tst_unary(a);
        for (int64_t b : vs) {
            tst_binary(a, b);
            tst_gcd(a, b);
        }
    }
    // gcd on small values, including negatives and zero.
    for (int64_t a = -30; a <= 30; ++a)
        for (int64_t b = -30; b <= 30; ++b)
            tst_gcd(a, b);
    // random pairs, and random pairs with a common factor for larger gcds
    random_gen rand(0);
    for (unsigned i = 0; i < 20000; ++i) {
        int64_t a = random_value(rand), b = random_value(rand);
        tst_binary(a, b);
        tst_gcd(a, b);
        // |g| < 2^31 and |u|, |v| < 2^32, so g * u and g * v do not overflow
        int64_t g = static_cast<int64_t>(rand.next_uint32() >> (1 + rand() % 31));
        int64_t u = static_cast<int64_t>(rand.next_uint32() >> (rand() % 32)) * (rand() % 2 ? -1 : 1);
        int64_t v = static_cast<int64_t>(rand.next_uint32() >> (rand() % 32)) * (rand() % 2 ? -1 : 1);
        tst_gcd(g * u, g * v);
    }
    std::cout << "checked_int64: " << s_failures << " failures\n";
    ENSURE(s_failures == 0);
}
