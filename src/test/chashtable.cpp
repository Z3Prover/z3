/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    chashtable.cpp

Abstract:

    Hashtable with chaining.  
    
Author:

    Leonardo de Moura (leonardo) 2011-04-14.

Revision History:

--*/
#include"chashtable.h"
#include"hashtable.h"
#include"hash.h"
#include"util.h"

typedef chashtable<int, int_hash, default_eq<int> > int_table;
typedef cmap<int, int, int_hash, default_eq<int> > int_map;

template class chashtable<int, int_hash, default_eq<int> >;
template class cmap<int, int, int_hash, default_eq<int> >;

template<typename T>
static void display(T const & beg, T const & end) {
    for (T it = beg; it != end; ++it)
        std::cout << *it << " ";
    std::cout << "\n";
}

static void tst1() {
    int_table t;
    t.insert(10);
    SASSERT(t.contains(10));
    t.insert(20);
    SASSERT(t.contains(20));
    t.insert(30);
    SASSERT(t.contains(30));
    SASSERT(t.size() == 3);
    display(t.begin(), t.end());
    t.erase(20);
    SASSERT(!t.contains(20));
    SASSERT(t.size() == 2);
}

struct dummy_hash {
    unsigned operator()(int v) const { return v % 2; }
};

typedef chashtable<int, dummy_hash, default_eq<int> > dint_table;

template class chashtable<int, dummy_hash, default_eq<int> >;

static void tst2() {
    dint_table t;
    t.insert(10);
    t.insert(12);
    SASSERT(t.used_slots() == 1);
    display(t.begin(), t.end());
    t.insert(13);
    display(t.begin(), t.end());
    SASSERT(t.used_slots() == 2);
    t.insert(14);
    SASSERT(t.used_slots() == 2);
    SASSERT(t.size() == 4);
    display(t.begin(), t.end());
    t.erase(12);
    SASSERT(!t.contains(12));
    SASSERT(t.size() == 3);
    SASSERT(t.contains(10));
    SASSERT(!t.contains(12));
    SASSERT(t.contains(14));
    SASSERT(t.contains(13));
    t.insert(16);
    SASSERT(t.size() == 4);
    t.insert(18);
    SASSERT(t.size() == 5);
    SASSERT(t.used_slots() == 2);
    display(t.begin(), t.end());
    t.erase(10);
    display(t.begin(), t.end());
    SASSERT(!t.contains(10));
    SASSERT(!t.contains(12));
    SASSERT(t.contains(14));
    SASSERT(t.contains(13));
    SASSERT(t.contains(16));
    SASSERT(t.contains(18));
}

static void tst3() {
    dint_table t;
    t.insert(10);
    t.insert(12);
    SASSERT(t.used_slots() == 1);
    SASSERT(t.contains(10));
    SASSERT(t.contains(12));
    t.erase(12);
    t.erase(10);
    SASSERT(t.size() == 0);
    SASSERT(t.empty());
    SASSERT(t.used_slots() == 0);
    t.insert(10);
    SASSERT(t.used_slots() == 1);
    SASSERT(t.contains(10));
    SASSERT(t.size() == 1);
}

typedef int_hashtable<int_hash, default_eq<int> > int_set;

template<typename T>
static void tst4(unsigned num, unsigned N) {
    int_set s;
    T       t;
    for (unsigned i = 0; i < num; i++) {
        int v = rand() % N;
        if (rand() % 3 == 2) {
            TRACE("chashtable", tout << "erase " << v << "\n";);
            s.erase(v);
            t.erase(v);
            SASSERT(!t.contains(v));
        }
        else {
            TRACE("chashtable", tout << "insert " << v << "\n";);
            s.insert(v);
            t.insert(v);
            SASSERT(t.contains(v));
        }
        SASSERT(s.size() == t.size());
        SASSERT(s.empty() == t.empty());
    }
    std::cout << "size: " << s.size() << " " << t.size() << "\n";
    int_set::iterator it1  = s.begin();
    int_set::iterator end1 = s.end();
    for(; it1 != end1; ++it1) {
        SASSERT(t.contains(*it1));
    }

    typename T::iterator it2  = t.begin();
    typename T::iterator end2 = t.end();
    for(; it2 != end2; ++it2) {
        SASSERT(s.contains(*it2));
        SASSERT(t.contains(*it2));
    }
}

static void tst5() {
    dint_table t;
    t.insert(4);
    t.insert(9);
    t.insert(8);
    t.insert(1);
    t.erase(1);
    t.insert(7);
    t.insert(1);
    t.insert(2);
}

static void tst6() {
    int_map m;
    m.insert(10, 4);
    SASSERT(m.contains(10));
    DEBUG_CODE({
        int r;
        SASSERT(m.find(10, r) && r == 4);
    });
}

void tst_chashtable() {
    tst1();
    tst2();
    tst3();
    tst6();
    tst4<dint_table>(1000,10);
    tst4<dint_table>(10000,10);
    tst4<int_table>(50000,1000);
    tst5();
}
