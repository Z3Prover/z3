/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_hashtable.cpp

Abstract:

    Test hashtable module

Author:

    Leonardo de Moura (leonardo) 2006-09-12.

Revision History:

--*/
#ifdef _WINDOWS
#include<iostream>
#include<unordered_set>
#include<stdlib.h>

#include "util/hashtable.h"


struct int_hash_proc { unsigned operator()(int x) const { return x * 3; } };
typedef int_hashtable<int_hash_proc, default_eq<int> > int_set;
typedef std::unordered_set<int, std::hash_compare<int, std::less<int> > > safe_int_set;
// typedef safe_int_set int_set;

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
        safe_int_set::iterator it  = h2.begin();
        safe_int_set::iterator end = h2.end();
        for(; it != end; ++it) {
            ENSURE(contains(h1, *it));
        }
    }
    {
        int_set::iterator it = h1.begin();
        int_set::iterator end = h1.end();
        int n = 0;
        for (; it != end; ++it) {
            ENSURE(contains(h1, *it));
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

void tst_hashtable() {
    tst3();
    for (int i = 0; i < 100; i++) 
        tst2();
    tst1();
}
#else
void tst_hashtable() {
}
#endif
