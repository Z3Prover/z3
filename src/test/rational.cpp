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
    TRACE("rational", tout << rational(3,4) << "\n";);
    TRACE("rational", tout << rational(7,9) << "\n";);
    TRACE("rational", tout << rational(-3,7) << "\n";);
    TRACE("rational", tout << rational(5,8) << "\n";);
    TRACE("rational", tout << rational(4,2) << "\n";);
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
    TRACE("rational", tout << r1 << std::endl;);
    TRACE("rational", tout << r2 << std::endl;);
    TRACE("rational", tout << r3 << std::endl;);

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
    TRACE("rational", tout << "n1: " << n1 << "\n";);
    rational n2 = div(n1, rational(2));
    rational n3 = div(rational(2), n2);
    TRACE("rational", 
          tout << "n1: " << n1 << "\n";
          tout << "n2: " << n2 << "\n";
          tout << "n3: " << n3 << "\n";);
    rational n4 = n1 - rational(3);
    rational n5 = div(n4, rational(2));
    TRACE("rational", 
          tout << "n4: " << n4 << "\n";
          tout << "n5: " << n5 << "\n";);
    ENSURE(n5 == rational("2147483646"));
}

void tst4() {
    rational n1("4294967293");
    TRACE("rational", tout << "n1: " << n1 << "\n";);
    rational n2 = div(n1, rational(2));
}

void tst5() {
    rational n1(1);
    n1.neg();
    rational n2("4294967295");
    n1 /= n2;
    TRACE("rational", tout << n1 << " " << n2 << " " << n1.is_big() << " " << n2.is_big() << "\n";);
    n1 *= n2;
    TRACE("rational", tout << "after: " << n1 << " " << n2 << "\n";);
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
        for (int i = 0; i <= 10000; i++) {
            int r = rand() % INT_MAX;
            if (rand()%2 == 1) r = -r;
            tst_hash(r);
        }
    }
};

static void tst7() {
    rational p;
    p = power(rational(2), 32);
    for (unsigned i = 1; i < 1000; i++) {
        rational n(i);
        rational x;
        rational y;
        rational gcd;
        extended_gcd(n, p, gcd, x, y);
        TRACE("gcd", tout << n << " " << p << ": " << gcd << " " << x << " " << y << "\n";);
        ENSURE(!mod(n, rational(2)).is_one() || mod(n * x, p).is_one()); 
    }
}

static void tst8() {
    rational r;
    ENSURE(!rational(-4).is_int_perfect_square(r) && r.is_zero());
    ENSURE(!rational(-3).is_int_perfect_square(r) && r.is_zero());
    ENSURE(!rational(-2).is_int_perfect_square(r) && r.is_zero());
    ENSURE(!rational(-1).is_int_perfect_square(r) && r.is_zero());
    ENSURE(rational(0).is_int_perfect_square(r) && r.is_zero());
    ENSURE(rational(1).is_int_perfect_square(r) && r.is_one());
    ENSURE(!rational(2).is_int_perfect_square(r) && r == rational(2));
    ENSURE(!rational(3).is_int_perfect_square(r) && r == rational(2));
    ENSURE(rational(4).is_int_perfect_square(r) && r == rational(2));
    ENSURE(!rational(5).is_int_perfect_square(r) && r == rational(3));
    ENSURE(!rational(6).is_int_perfect_square(r) && r == rational(3));
    ENSURE(!rational(7).is_int_perfect_square(r) && r == rational(3));
    ENSURE(!rational(8).is_int_perfect_square(r) && r == rational(3));
    ENSURE(rational(9).is_int_perfect_square(r) && r == rational(3));
    ENSURE(!rational(10).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(11).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(12).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(13).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(14).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(15).is_int_perfect_square(r) && r == rational(4));
    ENSURE(rational(16).is_int_perfect_square(r) && r == rational(4));
    ENSURE(!rational(17).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(18).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(19).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(20).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(21).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(22).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(23).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(24).is_int_perfect_square(r) && r == rational(5));
    ENSURE(rational(25).is_int_perfect_square(r) && r == rational(5));
    ENSURE(!rational(26).is_int_perfect_square(r) && r == rational(6));
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
    for (unsigned i = 0; i < NUM_RATIONALS; i++) {
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
        for (unsigned i = 0; i < NUM_RATIONALS - 1; i++) {
            vals[i] *= vals[i+1];
        }
    }
    {
        timeit t(true, "multiplication with floats: ");
        for (unsigned i = 0; i < NUM_RATIONALS - 1; i++) {
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
    for (unsigned i = 0; i < NUM_RATIONALS2; i++) {
        int r1 = rand() % MAGNITUDE2;
        int r2 = use_ints ? 1 : rand() % MAGNITUDE2;
        if (r2 == 0) r2 = 1;
        if (rand() % 2 == 0) r1 = -r1;
        vals[i]  = rational(r1, r2);
        fvals[i] = ((float)r1) / ((float)r2);
    }
    {
        timeit t(true, "multiplication with big rationals");
        for (unsigned j = 0; j < 10; j++)
            for (unsigned i = 0; i < NUM_RATIONALS2-1; i++) {
                vals[i] *= vals[i+1];
            }
    }
    {
        timeit t(true, "multiplication with floats: ");
        for (unsigned j = 0; j < 10; j++)
            for (unsigned i = 0; i < NUM_RATIONALS2-1; i++) {
                fvals[i] *= fvals[i+1];
            }
    }
    std::cout << "\n";
}

static void tst12() {
    std::cout << "test12\n";
    rational r;
    r = 5;
    SASSERT(r.get_bit(0));
    SASSERT(!r.get_bit(1));
    SASSERT(r.get_bit(2));
    SASSERT(!r.get_bit(3));
    r = rational("10000000000000000000000000000000001");
    for (unsigned i = 0; i < r.get_num_bits(); ++i)
        std::cout << i << ": " << r.get_bit(i) << "\n";
}


void tst_rational() {
    TRACE("rational", tout << "starting rational test...\n";);
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
    tst11(true);
    tst10(true);
    tst10(false);
    tst12();
}
