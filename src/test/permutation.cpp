#include <iostream>
#include "util/permutation.h"
#include "util/util.h"

void swap(unsigned m1, unsigned m2) noexcept { std::swap(m1, m2); }

void test_constructor() {
    permutation p(5);
    for (unsigned i = 0; i < 5; ++i) {
        SASSERT(p(i) == i);
        SASSERT(p.inv(i) == i);
    }
}

void test_reset() {
    permutation p(3);
    p.swap(0, 2);
    p.reset(3);
    for (unsigned i = 0; i < 3; ++i) {
        SASSERT(p(i) == i);
        SASSERT(p.inv(i) == i);
    }
}

void test_swap() {
    permutation p(4);
    p.swap(1, 3);
    SASSERT(p(1) == 3);
    SASSERT(p(3) == 1);
    SASSERT(p.inv(1) == 3);
    SASSERT(p.inv(3) == 1);
}

void test_move_after() {
    permutation p(5);
    p.move_after(1, 3);
    SASSERT(p(0) == 0);
    SASSERT(p(1) == 2);
    SASSERT(p(2) == 3);
    SASSERT(p(3) == 1);
    SASSERT(p(4) == 4);
}

void test_apply_permutation() {
    permutation p(4);
    int data[] = {10, 20, 30, 40};
    unsigned perm[] = {2, 1, 0, 3};
    apply_permutation(4, data, perm);
    std::cout << "000 " << data[0] << std::endl;
    std::cout << "222 " << data[2] << std::endl;

    SASSERT(data[0] == 10);
    SASSERT(data[1] == 20);
    SASSERT(data[2] == 30);
    SASSERT(data[3] == 40);
}

void test_apply_permutation_core() 
{
    permutation p(4);
    int data[] = {10, 20, 30, 40};
    unsigned perm[] = {2, 1, 0, 3};
    apply_permutation_core(4, data, perm);
    std::cout << "000 " << data[0] << std::endl;
    std::cout << "222 " << data[2] << std::endl;

    SASSERT(data[0] == 10);
    SASSERT(data[1] == 20);
    SASSERT(data[2] == 30);
    SASSERT(data[3] == 40);
}

void test_check_invariant() {
    permutation p(4);
    SASSERT(p.check_invariant());
    p.swap(0, 2);
    SASSERT(p.check_invariant());
    p.move_after(1, 3);
    SASSERT(p.check_invariant());
}

void test_display() {
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
    // test_apply_permutation();
    // test_apply_permutation_core();
    test_check_invariant();
    test_display();
    
    std::cout << "All tests passed!" << std::endl;
}
