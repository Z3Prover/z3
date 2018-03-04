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
#include "util/util.h"
#include "util/heap.h"
#include "util/trace.h"
#include "util/uint_set.h"
// include "util/hashtable.h"

struct lt_proc { bool operator()(int v1, int v2) const { return v1 < v2; } };
//struct int_hash_proc { unsigned operator()(int v) const { std::cout << "hash " << v << "\n"; VERIFY(v >= 0); return v; }};  
//typedef int_hashtable<int_hash_proc, default_eq<int> > int_set; 
typedef heap<lt_proc> int_heap;
#define N 10000

static random_gen heap_rand(1);

static void tst1() {
    int_heap h(N);
//    int_set t;
    uint_set  t;
    for (int i = 0; i < N * 3; i++) {
        int val = heap_rand() % N;
        if (!h.contains(val)) {
            ENSURE(!t.contains(val));
            h.insert(val);
            t.insert(val);
        }
        else {
            if (!t.contains(val)) {
                for (int v : t) std::cout << v << "\n";
            }
            ENSURE(t.contains(val));
        }
    }
    ENSURE(h.check_invariant());
    for (int v : t) {
        ENSURE(h.contains(v));
    }
    while (!h.empty()) {
        int m1 = h.min_value();
        int m2 = h.erase_min();
        (void)m1;
        (void)m2;
        ENSURE(m1 == m2);
        ENSURE(-1 < m2);
    }
}

int g_value[N];

struct lt_proc2 { bool operator()(int v1, int v2) const { ENSURE(v1 < N && v2 < N); return g_value[v1] < g_value[v2]; } };
typedef heap<lt_proc2> int_heap2;

static void init_values() {
    for (unsigned i = 0; i < N; i++) 
        g_value[i] = heap_rand();
}

#ifdef _TRACE
static void dump_heap(const int_heap2 & h, std::ostream & out) {
    //   int_heap2::const_iterator it  = h.begin();
    //   int_heap2::const_iterator end = h.end();
    //   for (; it != end; ++it) {
    //     out << *it << ":" << g_value[*it] << " ";
    //   }
    //   out << "\n";
}
#endif

static void tst2() {
    int_heap2 h(N);
    for (int i = 0; i < N * 10; i++) {

        if (i % 1 == 0) std::cout << "i: " << i << std::endl;
        if (i % 1000 == 0) std::cout << "i: " << i << std::endl;
        int cmd = heap_rand() % 10;
        if (cmd <= 3) {
            // insert
            int val = heap_rand() % N;
            if (!h.contains(val)) {
                TRACE("heap", tout << "inserting: " << val << "\n";);
                h.insert(val);
                TRACE("heap", dump_heap(h, tout););
                ENSURE(h.contains(val));
            }
        }
        else if (cmd <= 6) {
            int val = heap_rand() % N;
            if (h.contains(val)) {
                TRACE("heap", tout << "removing: " << val << "\n";);
                h.erase(val);
                TRACE("heap", dump_heap(h, tout););
                ENSURE(!h.contains(val));
            }
        }
        else if (cmd <= 8) {
            // increased & decreased
            int val = heap_rand() % N;
            int old_v = g_value[val];
            int new_v = heap_rand();
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
            ENSURE(h.check_invariant());
        }
    }
    ENSURE(h.check_invariant());
}

void tst_heap() {
    // enable_debug("heap");
    enable_trace("heap");
    unsigned i = 0;
    while (i < 3) {
        IF_VERBOSE(1, verbose_stream() << "test\n";);
        heap_rand.set_seed(i++);
        tst1();
        init_values();
        tst2();
    }
}

