/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    total_order.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-07-01.

Revision History:

--*/

#include "util/total_order.h"
#include "util/timeit.h"

static void tst1() {
    uint_total_order to;
    to.insert(1);
    to.insert_after(1, 2);
    to.insert_after(1, 3);
    ENSURE(to.lt(1, 2));
    ENSURE(to.lt(3, 2));
    ENSURE(to.lt(1, 3));
    ENSURE(!to.lt(2, 3));
    ENSURE(!to.lt(3, 1));
    ENSURE(!to.lt(2, 2));
    std::cout << to << "\n";
}

static void tst2() {
    uint_total_order to;
    to.insert(1);
    to.insert_after(1, 2);
    to.insert_after(2, 3);
    for (unsigned i = 0; i < 1000; i++) {
        to.move_after(3, 1);
        to.move_after(1, 2);
        to.move_after(2, 3);
        ENSURE(to.lt(1,2));
        ENSURE(to.lt(2,3));
    }
}

static void tst3(unsigned sz, unsigned num_rounds) {
    uint_total_order to;
    to.insert(0);
    for (unsigned i = 0; i < sz; i++) {
        to.insert_after(i, i+1);
    }
    for (unsigned i = 0; i < num_rounds; i++) {
        unsigned v1 = rand() % sz;
        unsigned v2 = rand() % sz;
        if (v1 != v2)
            to.move_after(v1, v2);
        if (i % 1000 == 0) {
            std::cout << "*";
            std::cout.flush();
        }
    }
    std::cout << std::endl;
}

void move_after(unsigned_vector & v, unsigned_vector & inv_v, unsigned a, unsigned b) {
    if (a == b)
        return;
    // std::cout << std::endl;
    // display(std::cout, v.begin(), v.end()); std::cout << std::endl;
    // std::cout << "move_after(" << a << ", " << b << ")\n";
    unsigned pos_a = inv_v[a];
    unsigned pos_b = inv_v[b];
    ENSURE(pos_a != pos_b);
    if (pos_b < pos_a) {
        for (unsigned i = pos_b; i < pos_a; i++) {
            v[i] = v[i+1];
            inv_v[v[i+1]] = i;
        }
        v[pos_a] = b;
        inv_v[b] = pos_a;
        ENSURE(inv_v[b] == inv_v[a] + 1);
    }
    else {
        ENSURE(pos_b > pos_a);
        for (unsigned i = pos_b; i > pos_a + 1; i--) {
            v[i] = v[i-1];
            inv_v[v[i-1]] = i;
        }
        v[pos_a+1] = b;
        inv_v[b]   = pos_a+1;
        ENSURE(inv_v[b] == inv_v[a] + 1);
    }
    // display(std::cout, v.begin(), v.end()); std::cout << std::endl;
}

static void tst4(unsigned sz, unsigned num_rounds) {
    uint_total_order to;
    unsigned_vector  v;
    unsigned_vector  inv_v;
    to.insert(0);
    v.push_back(0);
    inv_v.push_back(0);
    for (unsigned i = 0; i < sz; i++) {
        to.insert_after(i, i+1);
        v.push_back(i+1);
        inv_v.push_back(i+1);
    }
    for (unsigned i = 0; i < num_rounds; i++) {
        unsigned v1 = rand() % sz;
        unsigned v2 = rand() % sz;
        if (v1 != v2) {
            to.move_after(v1, v2); 
            move_after(v, inv_v, v1, v2);
        }
        for (unsigned k = 0; k < sz - 1; k++) {
            ENSURE(inv_v[v[k]] == k);
            ENSURE(to.lt(v[k], v[k+1]));
        }
        if (i % 1000 == 0) {
            std::cout << "*";
            std::cout.flush();
        }
    }
    std::cout << std::endl;
}

static void bad_case(unsigned sz, unsigned num_rounds) {
    uint_total_order to;
    to.insert(0);
    for (unsigned i = 0; i < sz; i++) {
        to.insert_after(i, i+1);
    }
    for (unsigned i = 0; i < num_rounds; i++) {
        to.move_after(sz, 0);
        for (unsigned j = 0; j < sz; j++) {
            to.move_after(j, j+1);
        }
        if (i % 10 == 0) {
            std::cout << "*";
            std::cout.flush();
        }
    }
    std::cout << std::endl;
}


void tst_total_order() {
    bad_case(100, 1000);
    tst1();
    tst2();
    tst4(3,    1000000);
    tst4(100,  100000);
    tst4(512,  100000);
    tst4(1000, 100000);
    tst3(100,  100000);
    tst3(1000, 100000);
}
