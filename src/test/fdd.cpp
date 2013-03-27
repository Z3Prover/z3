#include "fdd.h"

static void test1() {
    fdd::manager m;

    m.reset(2);
    int64 keys1[2] = { 1, 2 };
    m.insert(keys1);
    m.display(std::cout << "test1\n");
}

static void test2() {
    fdd::manager m;

    m.reset(2);
    int64 keys2[2] = { 2, 1 };
    m.insert(keys2);
    m.display(std::cout << "test2\n");

}

static void test3() {
    fdd::manager m;

    m.reset(2);
    int64 keys1[2] = { 1, 2 };
    int64 keys2[2] = { 2, 1 };
    m.insert(keys1);
    m.insert(keys2);
    m.display(std::cout << "test3\n");
}

static void test4() {
    fdd::manager m;

    std::cout << "test4\n";

    m.reset(2);
    int64 keys1[2] = { 1, 2 };
    int64 keys2[2] = { 2, 1 };
    int64 keys3[2] = { 1, 1 };
    int64 keys4[2] = { 2, 2 };
    int64 keys5[2] = { 2, 3 };
    int64 keys6[2] = { 3, 1 };
    int64 keys7[2] = { 3, 4 };
    m.insert(keys1);
    m.insert(keys2);
    std::cout << m.find_le(keys1) << "\n";
    std::cout << m.find_le(keys2) << "\n";
    std::cout << m.find_le(keys3) << "\n";
    std::cout << m.find_le(keys4) << "\n";
    std::cout << m.find_le(keys5) << "\n";
    std::cout << m.find_le(keys6) << "\n";
    std::cout << m.find_le(keys7) << "\n";

    SASSERT(m.find_le(keys1));
    SASSERT(m.find_le(keys2));
    SASSERT(!m.find_le(keys3));
    SASSERT(m.find_le(keys4));
    SASSERT(m.find_le(keys5));
    SASSERT(m.find_le(keys6));
    SASSERT(m.find_le(keys7));
}

static void test5() {
    fdd::manager m;

    std::cout << "test5\n";

    m.reset(2);
    int64 keys1[2] = { 1, 2 };
    int64 keys2[2] = { 2, 1 };
    m.insert(keys1);
    m.insert(keys2);
    m.insert(keys2);

    m.display(std::cout);

}

void tst_fdd() {
    test1();
    test2();
    test3();
    test4();
    test5();
}
