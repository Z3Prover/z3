/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    splay_tree.cpp

Abstract:

    Splay trees

Author:

    Leonardo de Moura (leonardo) 2008-01-31.

Revision History:

--*/

#include"splay_tree_map.h"
#include"splay_tree_def.h"
#include"trace.h"
#include"vector.h"
#include"map.h"
#include"timeit.h"

struct icomp {
    int operator()(int k1, int k2) const {
        return k1 - k2;
    }
};

struct visitor {
    bool     m_out;
    int      m_prev;
    unsigned m_num;

    visitor(bool f = true):m_out(f), m_prev(-1), m_num(0) {}

    void operator()(int k, int d) { 
        SASSERT(m_prev < k); 
        SASSERT(d == 2 * k); 
        m_num++; 
        m_prev = k;
        if (m_out) {
            TRACE_CODE(tout << k << " ";);
        }
    }
};

static void tst1(unsigned n) {
    splay_tree_map<int, int, icomp> s1;
    svector<bool> s2(n, false);
    unsigned       size = 0;

    unsigned num_op = rand()%1000;
    for (unsigned i = 0; i < num_op; i++) {
        unsigned op = rand()%5;
        if (op < 3) {
            unsigned idx = rand() % n;
            TRACE("splay_tree_detail", tout << "inserting: " << idx << "\n";);
            if (!s2[idx]) {
                size++;
            }
            s2[idx] = true;
            s1.insert(idx, idx*2);
        }
        else if (op < 4) {
            unsigned idx = rand() % n;
            TRACE("splay_tree_detail", tout << "erasing: " << idx << "\n";);
            if (s2[idx]) {
                size--;
            }
            s2[idx] = false;
            s1.erase(idx);
        }
        else {
            SASSERT((size == 0) == s1.empty());
            for (unsigned idx = 0; idx < n; idx++) {
                unsigned idx2 = rand() % n;
                DEBUG_CODE(
                    int v;
                    SASSERT(s2[idx2] == s1.find(idx2, v));
                    SASSERT(!s2[idx2] || v == 2*idx2);
                    );
            }
        }

        TRACE("splay_tree", 
              visitor v;
              s1.visit(v);
              tout << "\n";
              int idx = rand()%n;
              tout << "smaller than: " << idx << "\n";
              visitor v2;
              s1.visit_le(v2, idx);
              tout << "\n";
              tout << "greater than: " << idx << "\n";
              visitor v3;
              s1.visit_ge(v3, idx);
              tout << "\n";);

        visitor v(false);
        s1.visit(v);
        CTRACE("splay_tree", v.m_num != size, s1.display(tout); tout << "\n";);
        SASSERT(v.m_num == size);
    }
    s1.reset();
    SASSERT(s1.empty());
    TRACE("splay_tree", 
          visitor v;;
          s1.visit(v);
          SASSERT(v.m_num == 0);
          tout << "\n";);
}

static void tst_perf(int n1, int n2, int n3, int n4, int n5) {
    u_map<int> values1;
    svector<int> idxs;
    splay_tree_map<int, int, icomp> values2;

    {
        timeit t(true, "building: ");
        for (int i = 0; i < n2; i++) {
            int idx = rand() % n1;
            idxs.push_back(idx);
            values1.insert(idxs[i], i);
        }

        for (int i = 0; i < n2; i++) {
            values2.insert(idxs[i], i);
        }

    }
    
    int s1, s2;
    {
        timeit t(true, "u_map: ");
        s1 = 0;
        for (int j = 0; j < n4; j++) {
            for (int i = 0; i < n5; i++) {
                int v;
                values1.find(idxs[i], v);
                s1 += v;
            }
        }
    }
    std::cout << s1 << "\n";
    {
        timeit t(true, "splay_tree: ");
        s2 = 0;
        for (int j = 0; j < n4; j++) {
            for (int i = 0; i < n5; i++) {
                int v;
                values2.find(idxs[i], v);
                s2 += v;
            }
        }
        // for (int i = 0; i < n5; i++) {
        //    std::cout << idxs[i] << " ";
        // }
        std::cout << "\n";
        // values2.display(std::cout);
    }
    std::cout << s2 << "\n";

}

void tst_splay_tree() {
    for (unsigned i = 0; i < 100; i++) {
        tst1(1 + rand()%31);
        tst1(1 + rand()%100);
    }
    // tst_perf(10000000, 1000000, 10000, 1000000, 100);
}
