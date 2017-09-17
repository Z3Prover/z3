/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_bitvector.cpp

Abstract:

    Test bitvector module

Author:

    Leonardo de Moura (leonardo) 2006-10-03.

Revision History:

--*/
#include<cstdlib>
#include<iostream>
#include "util/bit_vector.h"
#include "util/vector.h"

static void tst1() {
    bit_vector     v1;
    svector<bool> v2;
    unsigned n = rand()%10000;
    for (unsigned i = 0; i < n; i++) {
        int op = rand()%6;
    if (op <= 1) {
        bool val = (rand()%2) != 0;
        v1.push_back(val);
        v2.push_back(val);
        ENSURE(v1.size() == v2.size());
    }
    else if (op <= 3) {
        ENSURE(v1.size() == v2.size());
        if (v1.size() > 0) {
        bool val = (rand()%2) != 0;
        unsigned idx = rand()%v1.size();
        ENSURE(v1.get(idx) == v2[idx]);
        v1.set(idx, val);
        v2[idx] = val;
        ENSURE(v1.get(idx) == v2[idx]);
        }
    }
    else if (op <= 4) {
        ENSURE(v1.size() == v2.size());
        if (v1.size() > 0) {
        unsigned idx = rand()%v1.size();
        VERIFY(v1.get(idx) == v2[idx]);
        }
    }
    else if (op <= 5) {
        ENSURE(v1.size() == v2.size());
        for (unsigned j = 0; j < v1.size(); j++) {
        ENSURE(v1.get(j) == v2[j]);
        }
    }
    }
}

static void tst2() {
    bit_vector b;
    b.push_back(true);
    b.push_back(false);
    b.push_back(true);
    b.resize(30);
    ENSURE(b.get(0) == true);
    ENSURE(b.get(1) == false);
    ENSURE(b.get(2) == true);
    ENSURE(b.get(3) == false);
    ENSURE(b.get(29) == false);
}

static void tst_shift() {
    bit_vector b;
    b.resize(111);
    b.set(105);
    b.set(99);
    b.set(98);
    b.set(90);
    b.set(80);
    b.set(75);
    b.set(33);
    b.set(32);
    b.set(31);
    b.set(30);
    b.set(10);
    std::cout << "b: " << b << "\n";
    b.shift_right(16);
    std::cout << "b: " << b << "\n";
    b.shift_right(1);
    std::cout << "b: " << b << "\n";
    b.shift_right(32);
    std::cout << "b: " << b << "\n";
    b.shift_right(42);
    std::cout << "b: " << b << "\n";
    b.shift_right(16);
    std::cout << "b: " << b << "\n";
    b.shift_right(63);
    std::cout << "b: " << b << "\n";
}

static void tst_or() {
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(5);
        b2.resize(10);
        b1.set(4);
        b2.set(8);
        b2.set(3);
        b2.set(2);
        b2.set(1);
        std::cout << b1 << "\n";
        std::cout << b2 << "\n";
        b1 |= b2;
        ENSURE(b1.size() == 10);
        std::cout << b1 << "\n";
        ENSURE(b1 != b2);
        ENSURE(b1 != b2);
        b1.unset(4);
        ENSURE(b1 == b2);
        b1.unset(3);
        ENSURE(b1 != b2);
    }
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(2);
        b2.resize(5);
        b1.set(0);
        b2.set(4);
        b1 |= b2;
        ENSURE(b1 != b2);
        b2.set(0);
        ENSURE(b1 == b2);
        std::cout << "-----\n";
        std::cout << b1 << "\n";
    }
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(10);
        b2.resize(10);
        b1.set(5);
        b2.set(8);
        b2.set(3);
        b2.resize(5);
        b1 |= b2;
        ENSURE(!b1.get(8));
        ENSURE(b1.get(5));
        ENSURE(b1.get(3));
    }
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(123);
        b2.resize(126);
        b2.set(124);
        b1.set(122);
        b1.set(100);
        b2.set(100);
        b1.set(80);
        b2.set(80);
        b1.set(4);
        b2.set(4);
        ENSURE(b1!=b2);
        b2.resize(123);
        ENSURE(b1!=b2);
        b1.resize(120);
        b2.resize(120);
        ENSURE(b1==b2);
        b1.unset(80);
        b1.unset(100);
        ENSURE(b1!=b2);
        b1 |= b2;
        ENSURE(b1 == b2);
    }
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(5);
        b2.resize(10);
        b2.set(8);
        b1.set(4);
        b2.set(1);
        b1.set(0);
        b1 |= b2;
        ENSURE(b1.size() == 10);
        ENSURE(b1.get(8) && b1.get(4) && b1.get(1) && b1.get(0) && !b1.get(9));
    }
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(32);
        b2.resize(32);
        b1.set(1);
        b1.set(5);
        b2.set(8);
        b2.set(0);
        b1 |= b2;
        ENSURE(b1.get(1) && b1.get(5) && b1.get(8) && b1.get(0) && !b1.get(11));
        std::cout << "b1(size32): " << b1 << "\n";
    }
}

static void tst_and() {
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(5);
        b2.resize(3);
        b2.set(2);
        b1.set(2);
        b1.set(4);
        std::cout << "------\nb1: " << b1 << "\n";
        b1 &= b2;
        std::cout << "------\nb1: " << b1 << "\n";
        ENSURE(!b1.get(4));
        ENSURE(b1.get(2));
    }
    {
        bit_vector b1;
        bit_vector b2;
        b1.resize(241);
        b2.resize(128);
        b1.set(240);
        b1.set(232);
        b1.set(127);
        b1.set(128);
        b1.set(8);
        b2.set(127);
        b2.set(5);
        b1 &= b2;
        ENSURE(!b1.get(240) && !b1.get(232) && !b1.get(128) && b1.get(127) && !b1.get(8) && !b1.get(5));
    }
}

static void tst_crash() {
    {
        bit_vector b;
        b.push_back(true);
        b.resize(64);
        ENSURE(!b.get(63));
        ENSURE(b.get(0));
        ENSURE(!b.get(1));
    }
    {
        bit_vector b;
        b.push_back(false);
        b.resize(64, true);
        ENSURE(b.get(63));
        ENSURE(!b.get(0));
        ENSURE(b.get(1));
    }
}

static void tst_bv_reset() {
    bit_vector b; 
    bool bit = true;
    for (unsigned sz = 1; sz < 84; ++sz) {
        b.reset();
        b.resize(sz, bit);        
        for (unsigned i = 0; i < sz; ++i) {
            ENSURE(bit == b.get(i));
        }
        for (unsigned sz2 = sz; sz2 < sz+10; ++sz2) {
            b.resize(sz2, !bit);        
            for (unsigned i = sz; i < sz2; ++i) {
                ENSURE(bit != b.get(i));
            }            
        }
        bit = !bit;
    }
}

static void tst_eq() {
    bit_vector b1, b2, b3;
    b1.resize(32);
    b2.resize(32);
    b3.resize(32);

    b1.set(3, true);
    ENSURE(b1 != b2);
    ENSURE(!(b1 == b2));
    ENSURE(b2 == b3);

    b3.set(3, true);
    ENSURE(b1 == b3);
    ENSURE(!(b1 != b3));
    
    b2.set(31, true);
    b3.set(31);
    b3.unset(3);
    ENSURE(b2 == b3);
    ENSURE(!(b2 != b3));
}

void tst_bit_vector() {
    tst_crash();
    tst_shift(); 
    tst_or();
    tst_and();
    tst_bv_reset();
    tst_eq();
    return;
    tst2();
    for (unsigned i = 0; i < 20; i++) {
        std::cerr << i << std::endl;
    tst1();
    }
}
