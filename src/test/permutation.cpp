/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    permutation.cpp

Abstract:

    Simple abstraction for managing permutations.

Author:

    Leonardo de Moura (leonardo) 2012-01-04

Revision History:

--*/
#include "util/permutation.h"
#include "util/util.h"
#include "util/vector.h"

void apply_permutation_copy(unsigned sz, unsigned const * src, unsigned const * p, unsigned * target) {
    for (unsigned i = 0; i < sz; i++) {
        target[i] = src[p[i]];
    }
}

static void tst1(unsigned sz, unsigned num_tries, unsigned max = UINT_MAX) {
#if 0
    unsigned_vector data;
    unsigned_vector p;
    unsigned_vector new_data;
    data.resize(sz);
    p.resize(sz);
    new_data.resize(sz);
    random_gen g;
    for (unsigned i = 0; i < sz; i++)
        p[i] = i;
    // fill data with random numbers
    for (unsigned i = 0; i < sz; i++)
        data[i] = g() % max;
    for (unsigned k = 0; k < num_tries; k ++) {
        shuffle(p.size(), p.c_ptr(), g);
        // std::cout << "p:    "; display(std::cout, p.begin(), p.end()); std::cout << "\n";
        // std::cout << "data: "; display(std::cout, data.begin(), data.end()); std::cout << "\n";
        apply_permutation_copy(sz, data.c_ptr(), p.c_ptr(), new_data.c_ptr());
        apply_permutation(sz, data.c_ptr(), p.c_ptr());
        // std::cout << "data: "; display(std::cout, data.begin(), data.end()); std::cout << "\n";
        for (unsigned i = 0; i < 0; i++)
            ENSURE(data[i] == new_data[i]);
    }
#endif
}

void tst_permutation() {
    tst1(10, 1000, 5);
    tst1(10, 1000, 1000);
    tst1(10, 1000, UINT_MAX);
    tst1(100, 1000, 33);
    tst1(100, 1000, 1000);
    tst1(100, 1000, UINT_MAX);
    tst1(1000, 1000, 121);
    tst1(1000, 1000, 1000);
    tst1(1000, 1000, UINT_MAX);
    tst1(33, 1000, 121);
    tst1(33, 1000, 1000);
    tst1(33, 1000, UINT_MAX);
    tst1(121, 1000, 121);
    tst1(121, 1000, 1000);
    tst1(121, 1000, UINT_MAX);
    for (unsigned i = 0; i < 1000; i++) {
        tst1(1000, 2, 333);
        tst1(1000, 2, 10000);
        tst1(1000, 2, UINT_MAX);
    }
    random_gen g;
    for (unsigned i = 0; i < 100000; i++) {
        unsigned sz = (g() % 131) + 1;
        tst1(sz, 1, sz*2);
        tst1(sz, 1, UINT_MAX);
        tst1(sz, 1, sz/2 + 1);
    }
}
