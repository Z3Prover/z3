#include "math/interval/mod_interval_def.h"

static void test_interval1() {
    mod_interval<uint64_t> i1(1, 2);
    mod_interval<uint64_t> i2(3, 6);
    std::cout << i1 << " " << i2 << "\n";
    std::cout << i1 << " * 4 := " << (i1 * 4) << "\n";
    std::cout << i2 << " * 3 := " << (i2 * 3) << "\n";
    std::cout << i1 << " * -4 := " << (i1 * (0 - 4)) << "\n";
    std::cout << i2 << " * -3 := " << (i2 * (0 - 3)) << "\n";
    std::cout << "-" << i2 << " := " << (-i2) << "\n";
}

static void test_interval2() {
    mod_interval<uint32_t> i;
    std::cout << " >= 0: " << i.intersect_uge(0) << "\n";
    std::cout << " >= 1: " << i.intersect_uge(1) << "\n";
    std::cout << " >= 2: " << i.intersect_uge(2) << "\n";
    SASSERT(i.lo == 2 && i.hi == 0);
    std::cout << " <= 10: " << i.intersect_ule(10) << "\n";
    std::cout << " > 2: " << i.intersect_ugt(2) << "\n";
    std::cout << " > 2: " << i.intersect_ugt(2) << "\n";
    std::cout << " <= 10: " << i.intersect_ule(10) << "\n";
    std::cout << " <= 11: " << i.intersect_ule(11) << "\n";
    std::cout << " <= 9: " << i.intersect_ule(9) << "\n";
    std::cout << " <= 2: " << i.intersect_ule(2) << "\n";
    SASSERT(i.is_empty());
    i = mod_interval<uint32_t>(2, 10);
    std::cout << " >= 10: " << i.intersect_uge(10) << "\n";
    SASSERT(i.is_empty());
    i = mod_interval<uint32_t>(500, 10);
    std::cout << "test-wrap: " << i << "\n";
}

void tst_mod_interval() {
    test_interval1();
    test_interval2();
}
