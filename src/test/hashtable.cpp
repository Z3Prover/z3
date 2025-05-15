/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_hashtable.cpp

Abstract:

    Test hashtable module

Author:

    Leonardo de Moura (leonardo) 2006-09-12.
    Chuyue Sun (liviasun) 2024-07-18.

Revision History:

--*/
#ifdef _WINDOWS
#include<iostream>
#include<unordered_set>
#include<stdlib.h>
#include "util/hashtable.h"


struct int_hash_proc { unsigned operator()(int x) const { return x * 3; } };
typedef int_hashtable<int_hash_proc, default_eq<int> > int_set;
// typedef safe_int_set int_set;
typedef std::unordered_set<int> safe_int_set;

inline bool contains(int_set & h, int i) {
    // return h.find(i) != h.end();
    return h.contains(i);
}

const int N = 10000;
int vals[N];

static void tst1() {
    int_set h1;
    int size = 0;
    for (int i = 1; i < N; i ++) {
        int v = rand() % (N / 2);
        h1.insert(v);
        vals[i] = v;
        ENSURE(contains(h1, v));
    }
    std::cout << "step1\n"; std::cout.flush();
    for (int i = 1; i < N; i ++) {
        ENSURE(contains(h1, vals[i]));
    }
    std::cout << "step2\n"; std::cout.flush();
    for (int i = 1; i < N; i += 2) {
        h1.erase(vals[i]);
        ENSURE(!contains(h1, vals[i]));
    }
    std::cout << "step3\n"; std::cout.flush();
    for (int i = 1; i < N; i += 2) {
        h1.insert(vals[i]);
    }  
    std::cout << "step4\n"; std::cout.flush();
    for (int i = 1; i < N; i ++) {
        ENSURE(contains(h1, vals[i]));
    }
}

static void tst2() {
    int_set      h1;
    safe_int_set h2;
    int N = rand() % 1000;
    for (int i = 0; i < N; i++) {
        int v = rand()%1000;
        if (rand() % 3 == 2) {
            h1.erase(v);
            h2.erase(v);
            ENSURE(!contains(h1, v));
        }
        else {
            h1.insert(v);
            h2.insert(v);
            ENSURE(contains(h1, v));
        }
    }
    { 
        for (const auto& elem : h2) {
            ENSURE(contains(h1, elem));
        }
    }
    {
        int n = 0;
        for (const auto& elem : h1) {
            ENSURE(contains(h1, elem));
            n++;
        }
        ENSURE(n == h1.size());
    }
    ENSURE(h1.size() == h2.size());
    // std::cout << "size: " << h1.size() << ", capacity: " << h1.capacity() << "\n"; std::cout.flush();
}

static void tst3() {
    int_set      h1;
    h1.insert(10);
    h1.insert(20);
    h1.insert(30);
    h1.erase(20);
    int_set    h2(h1);
    ENSURE(h1.contains(10));
    ENSURE(!h1.contains(20));
    ENSURE(h1.contains(30));
    ENSURE(h2.contains(10));
    ENSURE(!h2.contains(20));
    ENSURE(h2.contains(30));
    ENSURE(h2.size() == 2);
}

// Custom hash and equality functions for testing
struct my_hash {
    unsigned operator()(int x) const { return x; }
};

struct my_eq {
    bool operator()(int x, int y) const { return x == y; }
};

void test_hashtable_constructors() {
    hashtable<int, my_hash, my_eq> ht;
    VERIFY(ht.empty());
    VERIFY(ht.size() == 0);
    VERIFY(ht.capacity() == DEFAULT_HASHTABLE_INITIAL_CAPACITY);

    // Copy constructor
    hashtable<int, my_hash, my_eq> ht_copy(ht);
    VERIFY(ht_copy.empty());
    VERIFY(ht_copy.size() == 0);
    VERIFY(ht_copy.capacity() == ht.capacity());

    // Move constructor
    hashtable<int, my_hash, my_eq> ht_move(std::move(ht));
    VERIFY(ht_move.empty());
    VERIFY(ht_move.size() == 0);
    VERIFY(ht_move.capacity() == ht_copy.capacity());
}

void test_hashtable_insert() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    VERIFY(!ht.empty());
    VERIFY(ht.size() == 1);
    int value;
    VERIFY(ht.find(1, value) && value == 1);
}

void test_hashtable_remove() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    ht.remove(1);
    VERIFY(ht.empty());
    VERIFY(ht.size() == 0);
}

void test_hashtable_find() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    int value;
    VERIFY(ht.find(1, value) && value == 1);
    VERIFY(!ht.find(2, value));
}

void test_hashtable_contains() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    VERIFY(ht.contains(1));
    VERIFY(!ht.contains(2));
}

void test_hashtable_reset() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    ht.reset();
    VERIFY(ht.empty());
    VERIFY(ht.size() == 0);
}

void test_hashtable_finalize() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    ht.finalize();
    VERIFY(ht.empty());
    VERIFY(ht.size() == 0);
}

void test_hashtable_iterators() {
    hashtable<int, my_hash, my_eq> ht;
    ht.insert(1);
    ht.insert(2);
    ht.insert(3);
    
    int count = 0;
    for (const auto& elem : ht) {
        ++count;
    }
    VERIFY(count == 3);
}

void test_hashtable_operators() {
    hashtable<int, my_hash, my_eq> ht1;
    hashtable<int, my_hash, my_eq> ht2;
    
    ht1.insert(1);
    ht2.insert(2);
    
    ht1 |= ht2;
    VERIFY(ht1.contains(1));
    VERIFY(ht1.contains(2));
    
    ht1 &= ht2;
    VERIFY(!ht1.contains(1));
    VERIFY(ht1.contains(2));
}

void tst_hashtable() {
    tst3();
    for (int i = 0; i < 100; i++) 
        tst2();
    tst1();
    test_hashtable_constructors();
    test_hashtable_insert();
    test_hashtable_remove();
    test_hashtable_find();
    test_hashtable_contains();
    test_hashtable_reset();
    test_hashtable_finalize();
    test_hashtable_iterators();
    test_hashtable_operators();
    std::cout << "All tests passed!" << std::endl;
}
#else
void tst_hashtable() {
}
#endif
