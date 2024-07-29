#include <iostream>
#include "util/scoped_vector.h"

void test_push_back_and_access() {
    scoped_vector<int> sv;
    sv.push_back(10);
    
    sv.push_back(20);

    SASSERT(sv.size() == 2);
    SASSERT(sv[0] == 10);
    SASSERT(sv[1] == 20);
    
    std::cout << "test_push_back_and_access passed." << std::endl;
}

void test_scopes() {
    scoped_vector<int> sv;
    sv.push_back(10);
    sv.push_back(20);

    sv.push_scope();
    sv.push_back(30);
    sv.push_back(40);

    SASSERT(sv.size() == 4);
    SASSERT(sv[2] == 30);
    SASSERT(sv[3] == 40);

    sv.pop_scope(1);

    std::cout << "test_scopes passed." << std::endl;
    SASSERT(sv.size() == 2);
    SASSERT(sv[0] == 10);
    SASSERT(sv[1] == 20);

    std::cout << "test_scopes passed." << std::endl;
}

void test_set() {
    scoped_vector<int> sv;
    sv.push_back(10);
    sv.push_back(20);

    sv.set(0, 30);
    sv.set(1, 40);

    SASSERT(sv.size() == 2);
    SASSERT(sv[0] == 30);
    SASSERT(sv[1] == 40);

    sv.push_scope();
    sv.set(0, 50);
    SASSERT(sv[0] == 50);
    sv.pop_scope(1);
    SASSERT(sv[0] == 30);

    std::cout << "test_set passed." << std::endl;
}

void test_pop_back() {
    scoped_vector<int> sv;
    sv.push_back(10);
    sv.push_back(20);

    SASSERT(sv.size() == 2);
    sv.pop_back();
    SASSERT(sv.size() == 1);
    SASSERT(sv[0] == 10);
    sv.pop_back();
    SASSERT(sv.size() == 0);

    std::cout << "test_pop_back passed." << std::endl;
}

void test_erase_and_swap() {
    scoped_vector<int> sv;
    sv.push_back(10);
    sv.push_back(20);
    sv.push_back(30);

    sv.erase_and_swap(1);

    SASSERT(sv.size() == 2);
    SASSERT(sv[0] == 10);
    SASSERT(sv[1] == 30);

    std::cout << "test_erase_and_swap passed." << std::endl;
}

void tst_scoped_vector() {
    test_push_back_and_access();
    test_scopes();
    test_set();
    test_pop_back();
    test_erase_and_swap();

    std::cout << "All tests passed." << std::endl;
}
