/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_rational.cpp

Abstract:

    Test rationals

Author:

    Leonardo de Moura (leonardo) 2006-09-26.

Revision History:

--*/
#include<iostream>
#include<sstream>
#include<thread>
#include "util/vector.h"
#include "util/rational.h"
#include "util/trace.h"
#include "util/ext_gcd.h"
#include "util/timeit.h"

static void tst1() {
    rational r1(1);
    rational r2(1,2);
    rational r3(2,4);
    ENSURE(r2 == r3);
    ENSURE(r1 != r2);
    ENSURE(r2 + r3 == r1);
    ENSURE(r1.is_pos());
    ENSURE((r2 - r1).is_neg());
    ENSURE((r2 - r3).is_zero());
    ENSURE(floor(r2).is_zero());
    ENSURE(ceil(r2).is_one());
    // std::cout << "-r2: " << (-r2) << ", floor(-r2):" << floor(-r2) << "\n";
    ENSURE(floor(-r2).is_minus_one());
    ENSURE(ceil(-r2).is_zero());
    ENSURE(floor(r1) == r1);
    ENSURE(ceil(r1) == r1);
    rational r4(3,5);
    ENSURE(r3 * r4 == rational(3, 10));
    ENSURE(r3 / r4 == rational(5, 6));
    rational r5(2,3);
    ENSURE(r4 * r5 == rational(2, 5));
    --r2;
    ENSURE(r2 == -r3);
    r2.neg();
    ENSURE(r2 == r3);
    --r2;
    r2 = abs(r2);
    ENSURE(r2 == r3);
    --r2;
    ++r2;
    ENSURE(r2 == r3);
    ENSURE(r2 == abs(r2));
    ENSURE(r4 * rational(1) == r4);
    ENSURE((r4 * rational(0)).is_zero());
    ENSURE(r4 * rational(-1) == -r4);
    ENSURE(rational(1) * r4 == r4);
    ENSURE((rational(0) * r4).is_zero());
    ENSURE(rational(-1) * r4 == -r4);
    ENSURE(r4 + rational(0) == r4);
    ENSURE(ceil(r4).is_one());
    // std::cout << "r3: " << r3 << ", r4: " << r4 << ", -r4: " << -r4 << ", r3 / (-r4): " << (r3 / (-r4)) << "\n";
    ENSURE(r3 / (-r4) == rational(5,-6));
    ENSURE(div(rational(7), rational(2)) == rational(3));
    ENSURE(rational(7) % rational(4) == rational(3));
    ENSURE(div(rational(7), rational(-2)) == rational(-3));
    ENSURE(rational(3) + rational(5) == rational(8));
    ENSURE(rational("13/10") + rational("7/10") == rational(2));
    ENSURE(rational("100/20") == rational(5));
    ENSURE(gcd(rational(12), rational(8)) == rational(4));
    ENSURE(ceil(rational(-3,2)) == rational(-1));
    ENSURE(floor(rational(-3,2)) == rational(-2));
    ENSURE(ceil(rational(3,2)) == rational(2));
    ENSURE(floor(rational(3,2)) == rational(1));
    ENSURE(rational(3).is_pos());
    ENSURE(rational(0).is_nonneg());
    ENSURE(rational(3).is_pos());
    ENSURE(rational(3).is_nonneg());
    ENSURE(rational(0).is_nonneg());
    ENSURE(!rational(3).is_zero());
    ENSURE(!rational(-3).is_zero());
    ENSURE(rational(0).is_zero());
    ENSURE(rational(1).is_one());
    ENSURE(!rational(2).is_one());
    ENSURE(rational(3,4) >= rational(2,8));
    ENSURE(rational(3,4) <= rational(7,8));
    ENSURE(rational(3,4) <= rational(3,4));
    ENSURE(rational(3,4) >= rational(3,4));
    ENSURE(rational(3,4) >  rational(2,8));
    ENSURE(rational(3,4) <  rational(7,8));
    TRACE(rational, tout << rational(3,4) << "\n";);
    TRACE(rational, tout << rational(7,9) << "\n";);
    TRACE(rational, tout << rational(-3,7) << "\n";);
    TRACE(rational, tout << rational(5,8) << "\n";);
    TRACE(rational, tout << rational(4,2) << "\n";);
    ENSURE(rational(3) + rational(2) == rational(5));
    ENSURE(rational(3) - rational(2) == rational(1));
    ENSURE(rational(3) * rational(2) == rational(6));
    ENSURE(rational(6) / rational(2) == rational(3));
    ENSURE(rational(6) % rational(4) == rational(2));
    ENSURE(power(rational(2),0) == rational(1));
    ENSURE(power(rational(2),1) == rational(2));
    ENSURE(power(rational(2),3) == rational(8));    
}

static void tst2() {
    rational r1("10000000000000000000000000000000000");
    rational r2("10000000000000000000000000000000000/3");
    rational r3("20000000000000000000000000000000000/6");
    TRACE(rational, tout << r1 << std::endl;);
    TRACE(rational, tout << r2 << std::endl;);
    TRACE(rational, tout << r3 << std::endl;);

    ENSURE(r2 == r3);
    ENSURE(r1 != r2);
    ENSURE(rational(2)*r2 + r3 == r1);
    ENSURE(r1.is_pos());
    ENSURE((r2 - r1).is_neg());
    ENSURE((r2 - r3).is_zero());
    // std::cout << "===> " << floor(r2) << "\n";
    {
        rational r0("1/3000000000000000000000000");        
        ENSURE(ceil(r0).is_one());
        ENSURE(floor(-r0).is_minus_one());
        ENSURE(ceil(-r0).is_zero());
    }
    ENSURE(floor(r1) == r1);
    ENSURE(ceil(r1) == r1);
    rational r4("300000000/5");
    ENSURE(rational(1,2) * r4 == rational("300000000/10"));
    ENSURE(rational(1,2) / r4 == rational("5/600000000"));
    rational r5(2,3);
    ENSURE(r4 * r5 == rational("200000000/5"));
    rational r6("10000000000000000000000000000000003/3");
    --r6;
    ENSURE(r6 == r2);
    r6.neg();
    ENSURE(r6 != r2);
    ENSURE(abs(r6) == r2);
    --r2;
    ++r2;
    r2.neg();
    ENSURE(r2 == r6);
    ENSURE(r6 * rational(1) == r6);
    ENSURE((r6 * rational(0)).is_zero());
    ENSURE(r6 * rational(-1) == -r6);
    ENSURE(rational(1) * r6 == r6);
    ENSURE((rational(0) * r6).is_zero());
    ENSURE(rational(-1) * r6 == -r6);
    ENSURE(r6 + rational(0) == r6);

    ENSURE(rational("300000000000000").is_pos());
    ENSURE(rational("0000000000000000000").is_nonneg());
    ENSURE(rational("0000000000000000000").is_nonpos());
    ENSURE(rational("3000000000000000000/2").is_pos());
    ENSURE(rational("3000000000000000000/2").is_nonneg());
    ENSURE((-rational("3000000000000000000/2")).is_neg());
    ENSURE(!rational("3000000000000000000/2").is_neg());
    ENSURE(!rational("3000000000000000000/2").is_zero());
    ENSURE(!rational("3000000000000000000/2").is_one());
    ENSURE(rational("99999999999/2") >= rational("23/2"));
    ENSURE(rational("99999999999/2") > rational("23/2"));
    ENSURE(rational("23/2") <= rational("99999999999/2"));
    ENSURE(rational("23/2") < rational("99999999999/2"));
    ENSURE(!(rational("99999999999/2") < rational("23/2")));


    rational int64_max("9223372036854775807");
    rational int64_min((-int64_max) - rational(1));
    // is_int64
    ENSURE(int64_max.is_int64());
    ENSURE(int64_min.is_int64());
    ENSURE(rational(0).is_int64());
    ENSURE(rational(1).is_int64());
    ENSURE(rational(-1).is_int64());
    ENSURE(!(int64_max + rational(1)).is_int64());
    ENSURE(!(int64_min - rational(1)).is_int64());
    
    // is_uint64
    ENSURE(int64_max.is_uint64());
    ENSURE(!int64_min.is_uint64());
    ENSURE(rational(0).is_uint64());
    ENSURE(rational(1).is_uint64());
    ENSURE(!rational(-1).is_uint64());
    ENSURE((int64_max + rational(1)).is_uint64());
    ENSURE(!(int64_min - rational(1)).is_uint64());

    rational uint64_max(rational(1) + (rational(2) * int64_max));
    ENSURE(uint64_max.is_uint64());

    // get_int64, get_uint64
    uint64_t u1 = uint64_max.get_uint64();
    uint64_t u2 = UINT64_MAX;
    VERIFY(u1 == u2);
    std::cout << "int64_max: " << int64_max << ", INT64_MAX: " << INT64_MAX << ", int64_max.get_int64(): " << int64_max.get_int64() << ", int64_max.get_uint64(): " << int64_max.get_uint64() << "\n";
    ENSURE(int64_max.get_int64() == INT64_MAX);
    ENSURE(int64_min.get_int64() == INT64_MIN);

    // extended Euclid:
    
}

void tst3() {
    rational n1 = power(rational(2), 32);
    TRACE(rational, tout << "n1: " << n1 << "\n";);
    rational n2 = div(n1, rational(2));
    rational n3 = div(rational(2), n2);
    TRACE(rational, 
          tout << "n1: " << n1 << "\n";
          tout << "n2: " << n2 << "\n";
          tout << "n3: " << n3 << "\n";);
    rational n4 = n1 - rational(3);
    rational n5 = div(n4, rational(2));
    TRACE(rational, 
          tout << "n4: " << n4 << "\n";
          tout << "n5: " << n5 << "\n";);
    ENSURE(n5 == rational("2147483646"));
}

void tst4() {
    rational n1("4294967293");
    TRACE(rational, tout << "n1: " << n1 << "\n";);
    rational n2 = div(n1, rational(2));
}

void tst5() {
    rational n1(1);
    n1.neg();
    rational n2("4294967295");
    n1 /= n2;
    TRACE(rational, tout << n1 << " " << n2 << " " << n1.is_big() << " " << n2.is_big() << "\n";);
    n1 *= n2;
    TRACE(rational, tout << "after: " << n1 << " " << n2 << "\n";);
    ENSURE(n1.is_minus_one());
}

void tst6() {
    rational t1(5);
    rational t2(3);
    rational a, b, g;

    g = gcd(t1, t2, a, b);

    t1 = rational(15);
    t2 = rational(25);

    g = gcd(t1, t2, a, b);
    t1.neg();
    g = gcd(t1, t2, a, b);
    t2.neg();
    g = gcd(t1, t2, a, b);
    t1.neg();
    g = gcd(t1, t2, a, b);

    std::swap(t1, t2);

    g = gcd(t1, t2, a, b);
    t1.neg();
    g = gcd(t1, t2, a, b);
    t2.neg();
    g = gcd(t1, t2, a, b);
    t1.neg();
    g = gcd(t1, t2, a, b);

}

class rational_tester {
public:
    static void tst1() {
        rational n1(-1);
        rational n2(8);
        ENSURE((n1 % n2).is_minus_one());
        ENSURE(mod(n1, n2) == rational(7));
    }

    static void tst_hash(int val) {
        rational n1(val);
        rational n2("10203939394995449949494394932929");
        rational n3(val);
        n2 = n3;
        ENSURE(n1.hash() == n2.hash());
    }

    static void tst2() {
        tst_hash(0);
        for (int i = 0; i <= 10000; ++i) {
            int r = rand() % INT_MAX;
            if (rand()%2 == 1) r = -r;
            tst_hash(r);
        }
    }
};

static void tst7() {
    rational p;
    p = power(rational(2), 32);
    for (unsigned i = 1; i < 1000; ++i) {
        rational n(i);
        rational x;
        rational y;
        rational gcd;
        extended_gcd(n, p, gcd, x, y);
        TRACE(gcd, tout << n << " " << p << ": " << gcd << " " << x << " " << y << "\n";);
        ENSURE(!mod(n, rational(2)).is_one() || mod(n * x, p).is_one()); 
    }
}

static void tst8() {
    rational r;
    ENSURE(!rational(-4).is_int_perfect_square(r));
    ENSURE(!rational(-3).is_int_perfect_square(r));
    ENSURE(!rational(-2).is_int_perfect_square(r));
    ENSURE(!rational(-1).is_int_perfect_square(r));
    ENSURE(rational(0).is_int_perfect_square(r) && r.is_zero());
    ENSURE(rational(1).is_int_perfect_square(r) && r.is_one());
    ENSURE(!rational(2).is_int_perfect_square(r));
    ENSURE(!rational(3).is_int_perfect_square(r));
    ENSURE(rational(4).is_int_perfect_square(r) && r == rational(2));
    ENSURE(!rational(5).is_int_perfect_square(r));
    ENSURE(!rational(6).is_int_perfect_square(r));
    ENSURE(!rational(7).is_int_perfect_square(r));
    ENSURE(!rational(8).is_int_perfect_square(r));
    ENSURE(rational(9).is_int_perfect_square(r) && r == rational(3));
    ENSURE(!rational(10).is_int_perfect_square(r));
    ENSURE(!rational(11).is_int_perfect_square(r));
    ENSURE(!rational(12).is_int_perfect_square(r));
    ENSURE(!rational(13).is_int_perfect_square(r));
    ENSURE(!rational(14).is_int_perfect_square(r));
    ENSURE(!rational(15).is_int_perfect_square(r));
    ENSURE(rational(16).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(17).is_int_perfect_square(r));
    ENSURE(!rational(18).is_int_perfect_square(r));
    ENSURE(!rational(19).is_int_perfect_square(r));
    ENSURE(!rational(20).is_int_perfect_square(r));
    ENSURE(!rational(21).is_int_perfect_square(r));
    ENSURE(!rational(22).is_int_perfect_square(r));
    ENSURE(!rational(23).is_int_perfect_square(r));
    ENSURE(!rational(24).is_int_perfect_square(r));
    ENSURE(rational(25).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(26).is_int_perfect_square(r));
    ENSURE(rational(36).is_int_perfect_square(r) && r == rational(6));

    ENSURE(rational(1,9).is_perfect_square(r) && r == rational(1,3));
    ENSURE(rational(4,9).is_perfect_square(r) && r == rational(2,3));
}


static void tstmod(rational const& m, rational const& n) {
    //
    //   (=> (distinct n 0)
    //      (let ((q (div m n)) (r (mod m n)))
    //        (and (= m (+ (* n q) r))
    //             (<= 0 r (- (abs n) 1))))))
    //

    rational q = div(m,n);
    rational r = mod(m,n);
    std::cout << m << " " << n << " " << q << " " << r << "\n";
    std::cout << m << " == " << n*q+r << "\n";

    ENSURE(m == (n * q) + r);
    ENSURE(rational::zero() <= r);
    ENSURE(r < abs(n));

}

static void tst9() {
    // record semantics of rational div/mod.
    tstmod(rational("41000000000000"),rational("-7000000000000"));
    tstmod(rational("-41000000000000"),rational("-7000000000000"));
    tstmod(rational("-41000000000000"),rational("7000000000000"));
    tstmod(rational("41000000000000"),rational("7000000000000"));

    tstmod(rational(41),rational(-7));
    tstmod(rational(-41),rational(-7));
    tstmod(rational(-41),rational(7));
    tstmod(rational(41),rational(7));
}

#define NUM_RATIONALS 1000000
#define MAGNITUDE 10000

static void tst10(bool use_ints) {
    if (use_ints) 
        std::cout << "Testing multiplication performance using small ints\n";
    else
        std::cout << "Testing multiplication performance using small rationals\n";
    vector<rational> vals;
    vector<rational> vals2;
    vector<float>    fvals;
    vals.resize(NUM_RATIONALS);
    vals2.resize(NUM_RATIONALS);
    fvals.resize(NUM_RATIONALS);
    for (unsigned i = 0; i < NUM_RATIONALS; ++i) {
        int r1 = rand() % MAGNITUDE;
        int r2 = use_ints ? 1 : rand() % MAGNITUDE;
        if (r2 == 0) r2 = 1;
        if (rand() % 2 == 0) r1 = -r1;
        vals[i]  = rational(r1, r2);
        vals2[i]  = rational(r1, r2);
        fvals[i] = ((float)r1) / ((float)r2);
    }
    {
        timeit t(true, "multiplication with rationals");
        for (unsigned i = 0; i < NUM_RATIONALS - 1; ++i) {
            vals[i] *= vals[i+1];
        }
    }
    {
        timeit t(true, "multiplication with floats: ");
        for (unsigned i = 0; i < NUM_RATIONALS - 1; ++i) {
            fvals[i] *= fvals[i+1];
        }
    }
    std::cout << "\n";
}

#define NUM_RATIONALS2 10000
#define MAGNITUDE2 100000000

static void tst11(bool use_ints) {
    vector<rational> vals;
    vector<float>    fvals;
    vals.resize(NUM_RATIONALS2);
    fvals.resize(NUM_RATIONALS2);
    for (unsigned i = 0; i < NUM_RATIONALS2; ++i) {
        int r1 = rand() % MAGNITUDE2;
        int r2 = use_ints ? 1 : rand() % MAGNITUDE2;
        if (r2 == 0) r2 = 1;
        if (rand() % 2 == 0) r1 = -r1;
        vals[i]  = rational(r1, r2);
        fvals[i] = ((float)r1) / ((float)r2);
    }
    {
        timeit t(true, "multiplication with big rationals");
        for (unsigned j = 0; j < 10; ++j)
            for (unsigned i = 0; i < NUM_RATIONALS2-1; ++i) {
                vals[i] *= vals[i+1];
            }
    }
    {
        timeit t(true, "multiplication with floats: ");
        for (unsigned j = 0; j < 10; ++j)
            for (unsigned i = 0; i < NUM_RATIONALS2-1; ++i) {
                fvals[i] *= fvals[i+1];
            }
    }
    std::cout << "\n";
}

static void tst12() {
    std::cout << "test12\n";
    rational r;
    r = 5;
    ENSURE(r.get_bit(0));
    ENSURE(!r.get_bit(1));
    ENSURE(r.get_bit(2));
    ENSURE(!r.get_bit(3));
    r = rational("10000000000000000000000000000000001");
    for (unsigned i = 0; i < r.get_num_bits(); ++i)
        std::cout << i << ": " << r.get_bit(i) << "\n";
}

static void tst13() {
    std::cout << "test13\n";
    rational const step = rational(1) / rational(3);
    for (rational r; r < 5000; r += step) {
        {
            unsigned k = r.prev_power_of_two();
            if (r >= 1) {
                VERIFY(rational::power_of_two(k) <= r);
                VERIFY(r < rational::power_of_two(k + 1));
            }
            else {
                VERIFY_EQ(k, 0);
            }
        }
        {
            unsigned k = r.next_power_of_two();
            VERIFY(r <= rational::power_of_two(k));
            VERIFY(k == 0 || rational::power_of_two(k - 1) < r);
        }
    }
}

static void tst_compact_rational() {
    constexpr int limit = (1 << 30) - 1;
    rational const hi(limit), lo(-limit), big("123456789012345678901234567890123456789/37");
    ENSURE(sizeof(rational) == 8);
    ENSURE(hi + 1 == rational("1073741824"));
    ENSURE(lo - 1 == rational("-1073741824"));
    ENSURE((hi + 1) - hi == 1);
    ENSURE(rational(1, limit) / 2 == rational("1/2147483646"));
    ENSURE((rational(1, limit) / 2) * 2 == rational(1, limit));
    ENSURE(hi * hi == rational("1152921502459363329"));
    ENSURE(rational(limit, limit - 1) * rational(limit - 1, limit) == 1);
    ENSURE(rational(INT_MIN, INT_MIN) == 1);
    ENSURE(rational(INT_MIN, -1) == rational("2147483648"));
    ENSURE(rational(INT64_MIN) == rational("-9223372036854775808"));
    ENSURE(rational(UINT64_MAX) == rational("18446744073709551615"));
    ENSURE((big - big).is_zero());
    ENSURE((big / big).is_one());
    ENSURE((big * 0).is_zero());
    rational cancelled = big;
    cancelled -= big + rational("1073741824");
    ENSURE(cancelled == rational("-1073741824"));
    ENSURE(cancelled.hash() == rational("-1073741824").hash());
    bool caught = false;
    try {
        hi.expt((1 << 20) + 1);
    }
    catch (default_exception const&) {
        caught = true;
    }
    ENSURE(caught);
    ENSURE(rational(-1).expt(-1).is_minus_one());
    rational root(7);
    ENSURE(!rational(-1).is_int_perfect_square(root) && root == 7);
    std::ostringstream out;
    out << std::hex << rational(15, 16);
    ENSURE(out.str() == "15/16");
    {
        unsynch_mpq_manager manager;
        scoped_mpq exported(manager);
        big.export_mpq(manager, exported);
        ENSURE(rational(exported) == big);
        rational(1, 7).export_mpq(manager, exported);
        ENSURE(rational(exported) == rational(1, 7));
    }

    for (rational const& v : { rational(), rational(7, 13), hi, -hi, big, -big }) {
        rational c(v), d;
        d = c;
        c.neg();
        ENSURE(d == v);
        rational moved(std::move(d));
        ENSURE(moved == v && d.is_zero());
        d = std::move(moved);
        ENSURE(d == v && moved.is_zero());
        rational* alias = &d;
        d = *alias;
        ENSURE(d == v);
        d = std::move(*alias);
        ENSURE(d == v);
        rational twice = v + v;
        c = v; c += c; ENSURE(c == twice);
        c = v; c -= c; ENSURE(c.is_zero());
        c = v; c *= c; ENSURE(c == v * v);
        if (!v.is_zero()) { c = v; c /= c; ENSURE(c.is_one()); }
        swap(c, d);
        ENSURE(c == v);
        c.reset();
        ENSURE(c.is_zero());

        auto snapshot = v.to_mpq();
        rational source = v;
        mpq const& extended = source.to_mpq();
        source.reset();
        synch_mpq_manager qm;
        ENSURE(qm.eq(snapshot, extended));
        ENSURE(rational(snapshot) == v);
        ENSURE(v.hash() == qm.hash(snapshot));
        ENSURE(v.bitsize() == qm.bitsize(snapshot));
        ENSURE(v.storage_size() == qm.storage_size(snapshot));
        ENSURE(v.to_string() == qm.to_string(snapshot));
    }

    synch_mpq_manager qm;
    _scoped_numeral<synch_mpq_manager> a(qm), b(qm), expected(qm), roundtrip(qm);
    uint32_t seed = 17;
    auto next = [&]() { seed = 1664525u * seed + 1013904223u; return seed; };
    for (unsigned i = 0; i < 6000; ++i) {
        int n1 = std::bit_cast<int32_t>(next()), n2 = std::bit_cast<int32_t>(next());
        unsigned d1 = (next() % limit) + 1, d2 = (next() % limit) + 1;
        if (i % 3 == 0) { n1 /= 65536; n2 /= 65536; d1 %= 1024; ++d1; d2 %= 1024; ++d2; }
        if (i % 7 == 0) { d1 = 1; d2 = 1; }
        qm.set(a, int64_t(n1), uint64_t(d1));
        qm.set(b, int64_t(n2), uint64_t(d2));
        rational x(a), y(b);
        if (i % 11 == 0) {
            qm.mul(a, big.to_mpq(), a);
            x *= big;
        }
        ENSURE((x == y) == qm.eq(a, b));
        ENSURE((x < y) == qm.lt(a, b));
        auto check = [&](rational const& actual) {
            actual.export_mpq(qm, roundtrip);
            ENSURE(qm.eq(roundtrip, expected));
            ENSURE(actual.hash() == rational(expected).hash());
        };
        qm.add(a, b, expected); check(x + y);
        qm.sub(a, b, expected); check(x - y);
        qm.mul(a, b, expected); check(x * y);
        if (!y.is_zero()) { qm.div(a, b, expected); check(x / y); }
        qm.floor(a, expected); check(floor(x));
        qm.ceil(a, expected); check(ceil(x));
        if (x.is_int() && y.is_int() && !y.is_zero()) {
            qm.idiv(a, b, expected); check(div(x, y));
            rational alias = x;
            div(alias, y, alias); check(alias);
            qm.mod(a, b, expected); check(mod(x, y));
            alias = y; mod(x, alias, alias); check(alias);
            qm.rem(a, b, expected); check(x % y);
            qm.machine_idiv(a, b, expected); check(machine_div(x, y));
            rational rem;
            rational q = machine_div_rem(x, y, rem);
            check(q);
            ENSURE(q * y + rem == x);
            alias = x;
            q = machine_div_rem(alias, y, alias);
            check(q);
            ENSURE(q * y + alias == x);
        }
    }
#ifndef SINGLE_THREAD
    std::thread workers[4];
    for (auto& worker : workers) {
        worker = std::thread([&big]() {
            for (unsigned i = 1; i <= 100; ++i) {
                rational delta(1, i), a = big + delta, b(a);
                a -= big;
                ENSURE(a == delta);
                auto q = b.to_mpq();
                b.reset();
                ENSURE(rational(q) == big + delta);
            }
        });
    }
    for (auto& worker : workers) worker.join();
#endif
}


void tst_rational() {
    TRACE(rational, tout << "starting rational test...\n";);
    std::cout << "sizeof(rational): " << sizeof(rational) << "\n";
    rational r1("10000000000000000000000000000000001");
    r1.hash();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    std::cout << "running tst6" << std::endl;
    tst6();
    std::cout << "running tst7" << std::endl;
    tst7();
    std::cout << "running tst8" << std::endl;
    tst8();
    std::cout << "running tst9" << std::endl;
    tst9();
    std::cout << "running rational_tester::tst1" << std::endl;
    rational_tester::tst1();
    rational_tester::tst2();
    tst12();
    tst13();
    tst_compact_rational();
}

// Multiplication micro-benchmarks against floats. They only print timings and
// assert nothing, so they are not part of `test-z3 -a`; run as
// `test-z3 rational_perf`.
void tst_rational_perf() {
    tst11(true);
    tst10(true);
    tst10(false);
}
