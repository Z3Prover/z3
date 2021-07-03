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

void tst_mod_interval() {
    test_interval1();
}
