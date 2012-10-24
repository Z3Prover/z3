/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_heap.cpp

Abstract:

    Test heap template.

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

Revision History:

--*/
#include<iostream>
#include"heap.h"
#include"hashtable.h"
#include"trace.h"

struct lt_proc { bool operator()(int v1, int v2) const { return v1 < v2; } };
typedef heap<lt_proc> int_heap;
struct int_hash_proc { unsigned operator()(int v) const { return v * 17; }};
typedef int_hashtable<int_hash_proc, default_eq<int> > int_set;
#define N 10000

static void tst1() {
    int_heap h(N);
    int_set  t;
    for (int i = 0; i < N * 3; i++) {
        int val = rand() % N;
        if (!h.contains(val)) {
            SASSERT(!t.contains(val));
            h.insert(val);
            t.insert(val);
        }
        else {
            SASSERT(t.contains(val));
        }
    }
    SASSERT(h.check_invariant());
    int_set::iterator it  = t.begin();
    int_set::iterator end = t.end();
    for (; it != end; ++it) {
        SASSERT(h.contains(*it));
    }
    int last = -1;
    while (!h.empty()) {
        int m1 = h.min_value();
        int m2 = h.erase_min();
        SASSERT(m1 == m2);
        SASSERT(last < m2);
    }
}

int g_value[N];

struct lt_proc2 { bool operator()(int v1, int v2) const { SASSERT(v1 < N && v2 < N); return g_value[v1] < g_value[v2]; } };
typedef heap<lt_proc2> int_heap2;

static void init_values() {
    for (unsigned i = 0; i < N; i++) 
        g_value[i] = rand();
}

static void dump_heap(const int_heap2 & h, std::ostream & out) {
    //   int_heap2::const_iterator it  = h.begin();
    //   int_heap2::const_iterator end = h.end();
    //   for (; it != end; ++it) {
    //     out << *it << ":" << g_value[*it] << " ";
    //   }
    //   out << "\n";
}

static void tst2() {
    int_heap2 h(N);
    for (int i = 0; i < N * 10; i++) {
        if (i % 1000 == 0) std::cout << "i: " << i << std::endl;
        int cmd = rand() % 10;
        if (cmd <= 3) {
            // insert
            int val = rand() % N;
            if (!h.contains(val)) {
                TRACE("heap", tout << "inserting: " << val << "\n";);
                h.insert(val);
                TRACE("heap", dump_heap(h, tout););
                SASSERT(h.contains(val));
            }
        }
        else if (cmd <= 6) {
            int val = rand() % N;
            if (h.contains(val)) {
                TRACE("heap", tout << "removing: " << val << "\n";);
                h.erase(val);
                TRACE("heap", dump_heap(h, tout););
                SASSERT(!h.contains(val));
            }
        }
        else if (cmd <= 8) {
            // increased & decreased
            int val = rand() % N;
            int old_v = g_value[val];
            int new_v = rand();
            if (h.contains(val)) {
                g_value[val] = new_v;
                if (old_v < new_v) {
                    TRACE("heap", tout << "value of: " << val << " increased old: " << old_v << " new: " << new_v << "\n";);
                    h.increased(val);
                }
                else {
                    TRACE("heap", tout << "value of: " << val << " decreased old: " << old_v << " new: " << new_v << "\n";);
                    h.decreased(val);
                }
            }
        }
        else {
            SASSERT(h.check_invariant());
        }
    }
    SASSERT(h.check_invariant());
}

void tst_heap() {
    // enable_debug("heap");
    enable_trace("heap");
    tst1();
    init_values();
    tst2();
}

