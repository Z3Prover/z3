/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    uint_set.cpp

Abstract:

    Test sets of unsigned integers.

Author:

    Leonardo de Moura (leonardo) 2006-12-07.

Revision History:

--*/

#include "util/uint_set.h"
#include "util/vector.h"

static void tst1(unsigned n) {
    uint_set       s1;
    svector<bool>  s2(n, false);
    unsigned       size = 0;

    unsigned num_op = rand()%1000;
    for (unsigned i = 0; i < num_op; i++) {
        unsigned op = rand()%3;
        if (op < 2) {
            unsigned idx = rand() % n;
            if (!s2[idx]) {
                size++;
            }
            s2[idx] = true;
            s1.insert(idx);
        }
        else {
            unsigned idx = rand() % n;
            if (s2[idx]) {
                size--;
            }
            s2[idx] = false;
            s1.remove(idx);
        }
        ENSURE(s1.num_elems() == size);
        ENSURE((size == 0) == s1.empty());
        for (unsigned idx = 0; idx < n; idx++) {
            ENSURE(s2[idx] == s1.contains(idx));
        }
    }
}

static void tst2(unsigned n) {
    uint_set s;
    ENSURE(s.empty());
    unsigned val = rand()%n;
    s.insert(val);
    ENSURE(!s.empty());
    ENSURE(s.num_elems() == 1);
    for (unsigned i = 0; i < 100; i++) {
        unsigned val2 = rand()%n;
        if (val != val2) {
            ENSURE(!s.contains(val2));
        }
    }
    s.remove(val);
    ENSURE(s.num_elems() == 0);
    ENSURE(s.empty());
}

static void tst3(unsigned n) {
    ENSURE(n > 10);
    uint_set s1;
    uint_set s2;
    ENSURE(s1 == s2);
    s1.insert(3);
    ENSURE(s1.num_elems() == 1);
    ENSURE(s2.num_elems() == 0);
    ENSURE(s1 != s2);
    s2.insert(5);
    ENSURE(s2.num_elems() == 1);
    ENSURE(s1 != s2);
    ENSURE(!s1.subset_of(s2));
    s2 |= s1;
    ENSURE(s1.subset_of(s2));
    ENSURE(s2.num_elems() == 2);
    ENSURE(s1 != s2);
    s1 |= s2;
    ENSURE(s1.subset_of(s2));
    ENSURE(s2.subset_of(s1));
    ENSURE(s1.num_elems() == 2);
    ENSURE(s2.num_elems() == 2);
    ENSURE(s1 == s2);
    s1.insert(9);
    ENSURE(s1.num_elems() == 3);
    ENSURE(s2.num_elems() == 2);
    s1.insert(9);
    ENSURE(s1.num_elems() == 3);
    ENSURE(s2.num_elems() == 2);
    ENSURE(s2.subset_of(s1));
    ENSURE(!s1.subset_of(s2));
    ENSURE(s1 != s2);
    uint_set s3(s1);
    ENSURE(s1 == s3);
    ENSURE(s1.subset_of(s3));
    ENSURE(s3.subset_of(s1));
    ENSURE(s2 != s3);
    uint_set s4(s2);
    ENSURE(s2 == s4);
    ENSURE(s2.subset_of(s4));
    ENSURE(s4.subset_of(s2));
    ENSURE(s2 != s3);
    for (unsigned i = 0; i < n; i++) {
        uint_set s5;
        s5.insert(i);
        ENSURE(s1.contains(i) == s5.subset_of(s1));
    }
}

static void tst4() {
    uint_set s;
    s.insert(32);
    ENSURE(s.contains(32));
    ENSURE(!s.contains(31));
    ENSURE(!s.contains(0));
    s.remove(32);
    ENSURE(!s.contains(32));
    ENSURE(!s.contains(31));
    ENSURE(!s.contains(0));
}

#include "util/map.h"

template <typename Value>
struct uint_map : public map<uint_set, Value, uint_set::hash, uint_set::eq> {};

static void tst5() {
    uint_set s;
    std::cout << s.get_hash() << "\n";
    s.insert(1);
    std::cout << s.get_hash() << "\n";
    s.insert(2);
    std::cout << s.get_hash() << "\n";
    s.insert(44);
    std::cout << s.get_hash() << "\n";

    uint_map<unsigned> m;
    m.insert(s, 1);
    s.insert(4);
    m.insert(s, 3);
    uint_map<unsigned>::iterator it = m.begin(), end = m.end();
    for (; it != end; ++it) {
        std::cout << it->m_key << " : " << it->m_value << "\n";
    }
    
}

void tst_uint_set() {
    for (unsigned i = 0; i < 100; i++) {
        tst1(1 + rand()%31);
        tst1(1 + rand()%100);
    }
    for (unsigned i = 0; i < 1000; i++) {
        tst2(1);
        tst2(10);
        tst2(31);
        tst2(32);
        tst2(100);
    }
    tst3(12);
    tst3(100);
    tst4();
    tst5();
}

