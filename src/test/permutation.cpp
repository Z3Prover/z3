#include <iostream>
#include <sstream>
#include "util/permutation.h"
#include "util/util.h"
#include "util/debug.h"

 void swap(unsigned m1, unsigned m2) noexcept { std::swap(m1, m2); }

static void test_constructor() {
    permutation p(5);
    for (unsigned i = 0; i < 5; ++i) {
        SASSERT(p(i) == i);
        SASSERT(p.inv(i) == i);
    }
}

static void test_reset() {
    permutation p(3);
    p.swap(0, 2);
    p.reset(3);
    for (unsigned i = 0; i < 3; ++i) {
        SASSERT(p(i) == i);
        SASSERT(p.inv(i) == i);
    }
}

static void test_swap() {
    permutation p(4);
    p.swap(1, 3);
    SASSERT(p(1) == 3);
    SASSERT(p(3) == 1);
    SASSERT(p.inv(1) == 3);
    SASSERT(p.inv(3) == 1);
}

static void test_move_after() {
    permutation p(5);
    p.move_after(1, 3);
    SASSERT(p(0) == 0);
    SASSERT(p(1) == 2);
    SASSERT(p(2) == 3);
    SASSERT(p(3) == 1);
    SASSERT(p(4) == 4);
}

void apply_permutation_copy(unsigned sz, unsigned const * src, unsigned const * p, unsigned * target) {
    for (unsigned i = 0; i < sz; i++) {
        target[i] = src[p[i]];
    }
}

static void test_apply_permutation(unsigned sz, unsigned num_tries, unsigned max = UINT_MAX) {
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
        shuffle(p.size(), p.data(), g);
        apply_permutation_copy(sz, data.data(), p.data(), new_data.data());
        apply_permutation(sz, data.data(), p.data());
        for (unsigned i = 0; i < 0; i++)
            ENSURE(data[i] == new_data[i]);
    }
}


static void test_check_invariant() {
    permutation p(4);
    SASSERT(p.check_invariant());
    p.swap(0, 2);
    SASSERT(p.check_invariant());
    p.move_after(1, 3);
    SASSERT(p.check_invariant());
}

static void test_display() {
    permutation p(4);
    std::ostringstream out;
    p.display(out);
    SASSERT(out.str() == "0:0 1:1 2:2 3:3");
}

void tst_permutation() {
    test_constructor();
    test_reset();
    test_swap();
    test_move_after();
    test_check_invariant();
    test_display();
    test_apply_permutation(10, 1000, 5);
    test_apply_permutation(10, 1000, 1000);
    test_apply_permutation(10, 1000, UINT_MAX);
    test_apply_permutation(100, 1000, 33);
    test_apply_permutation(100, 1000, 1000);
    test_apply_permutation(100, 1000, UINT_MAX);
    test_apply_permutation(1000, 1000, 121);
    test_apply_permutation(1000, 1000, 1000);
    test_apply_permutation(1000, 1000, UINT_MAX);
    test_apply_permutation(33, 1000, 121);
    test_apply_permutation(33, 1000, 1000);
    test_apply_permutation(33, 1000, UINT_MAX);
    test_apply_permutation(121, 1000, 121);
    test_apply_permutation(121, 1000, 1000);
    test_apply_permutation(121, 1000, UINT_MAX);

    std::cout << "All tests passed!" << std::endl;
}
