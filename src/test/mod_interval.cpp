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
    std::cout << " >= 0: " << i.intersect_uge(0) << "\n";
    std::cout << " >= 2: " << i.intersect_uge(2) << "\n";
    std::cout << " >= 11: " << i.intersect_uge(11) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " >= 10: " <<  i << " -> " << i.intersect_uge(10) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " >= 499: " <<  i << " -> " << i.intersect_uge(499) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " >= 500: " << i << " -> " << i.intersect_uge(500) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " >= 501: " << i << " -> " << i.intersect_uge(501) << "\n";

    i = mod_interval<uint32_t>(500, 10);
    std::cout << " > 0: " << i.intersect_ugt(0) << "\n";
    std::cout << " > 2: " << i.intersect_ugt(2) << "\n";
    std::cout << " > 10: " << i.intersect_ugt(10) << "\n";
    std::cout << " > 11: " << i.intersect_ugt(11) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " > 10: " <<  i << " -> " << i.intersect_ugt(10) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " > 499: " <<  i << " -> " << i.intersect_ugt(499) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " > 500: " << i << " -> " << i.intersect_ugt(500) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " > 501: " << i << " -> " << i.intersect_ugt(501) << "\n";

    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 0: " << i.intersect_ule(0) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 2: " << i.intersect_ule(2) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 9: " << i.intersect_ule(9) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 10: " << i.intersect_ule(10) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 11: " << i.intersect_ule(11) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 499: " <<  i << " -> " << i.intersect_ule(499) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 500: " << i << " -> " << i.intersect_ule(500) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " <= 501: " << i << " -> " << i.intersect_ule(501) << "\n";


    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 0: " << i.intersect_ult(0) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 2: " << i.intersect_ult(2) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 9: " << i.intersect_ult(9) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 10: " << i.intersect_ult(10) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 11: " << i.intersect_ult(11) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 499: " <<  i << " -> " << i.intersect_ult(499) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 500: " << i << " -> " << i.intersect_ult(500) << "\n";
    i = mod_interval<uint32_t>(500, 10);
    std::cout << " < 501: " << i << " -> " << i.intersect_ult(501) << "\n";
}

static void test_interval_intersect(unsigned i, unsigned j, unsigned k, unsigned l) {
    if (i == j && i != 0)
        return;
    if (k == l && k != 0)
        return;
    mod_interval<uint8_t> x(i, j);
    mod_interval<uint8_t> y(k, l);
    auto r = x & y;
    bool x_not_y = false, y_not_x = false;
    // check that & computes a join
    // it contains all elements in x, y
    // it contains no elements neither in x, y
    // it does not contain two elements, one in x\y the other in y\x   
    for (i = 0; i < 256; ++i) {
        uint8_t c = (uint8_t)i;
        if ((x.contains(c) && y.contains(c)) &&  !r.contains(c)) {
            std::cout << x << " & " << y << " = " << r << "\n";
            std::cout << i << " " << r.contains(c) << " " << x.contains(c) << " " << y.contains(c) << "\n";
        }
        VERIFY(!(x.contains(c) && y.contains(c)) || r.contains(c));
        VERIFY(x.contains(c) || y.contains(c) || !r.contains(c));
        if (r.contains(c) && x.contains(c) && !y.contains(c))
            x_not_y = true;
        if (r.contains(c) && !x.contains(c) && y.contains(c))
            y_not_x = true;
    }
    if (x_not_y && y_not_x) {
        std::cout << x << " & " << y << " = " << r << "\n";
        VERIFY(!x_not_y || !y_not_x);
    }
}


static void test_interval_intersect() {
    unsigned bounds[8] = { 0, 1, 2, 3, 252, 253, 254, 255 };
    for (unsigned i = 0; i < 8; ++i)
        for (unsigned j = 0; j < 8; ++j)
            for (unsigned k = 0; k < 8; ++k)
                for (unsigned l = 0; l < 8; ++l)
                    test_interval_intersect(bounds[i], bounds[j], bounds[k], bounds[l]);
}

static void test_interval_intersect2(unsigned i, unsigned j, uint8_t k) {
    if (i == j && i != 0)
        return;
    mod_interval<uint8_t> x0(i, j);

    auto validate = [&](char const* t, mod_interval<uint8_t> const& y, mod_interval<uint8_t> const& z) {
        if (y == z)
            return;
        std::cout << t << "(" << (unsigned)k << ") " << x0 << " -> " << y << " " << z << "\n";
        SASSERT(false);
    };

    {
        mod_interval<uint8_t> x = x0;
        auto uge2 = x & mod_interval<uint8_t>(k, 0);
        auto uge1 = x.intersect_uge(k);
        validate("uge", uge1, uge2);
    }

    {
        mod_interval<uint8_t> x = x0;
        auto ule1 = x.intersect_ule(k);
        if ((uint8_t)(k + 1) != 0) {
            auto ule2 = x0 & mod_interval<uint8_t>(0, k + 1);
            validate("ule", ule1, ule2);
        }
        else {
            validate("ule", ule1, x0);
        }
    }

    {
        mod_interval<uint8_t> x = x0;
        auto ult1 = x.intersect_ult(k);
        if (k != 0) {
            auto ult2 = x0 & mod_interval<uint8_t>(0, k);
            validate("ult", ult1, ult2);
        }
        else {
            validate("ult", ult1, mod_interval<uint8_t>::empty());
        }
    }
    {
        mod_interval<uint8_t> x = x0;
        auto ugt1 = x.intersect_ugt(k);
        
        if ((uint8_t)(k + 1) != 0) {
            auto ugt2 = x0 & mod_interval<uint8_t>(k + 1, 0);
            validate("ugt", ugt1, ugt2);
        }
        else {
            validate("ugt", ugt1, mod_interval<uint8_t>::empty());
        }
    }
}


static void test_interval_intersect2() {
    unsigned bounds[8] = { 0, 1, 2, 3, 252, 253, 254, 255 };
    for (unsigned i = 0; i < 8; ++i)
        for (unsigned j = 0; j < 8; ++j)
            for (unsigned k = 0; k < 8; ++k)
                test_interval_intersect2(bounds[i], bounds[j], bounds[k]);
}


void tst_mod_interval() {
    test_interval_intersect();
    test_interval_intersect2();
    test_interval1();
    test_interval2();
}
