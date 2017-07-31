/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    stack.cpp

Abstract:
    Low level stack (aka stack-based allocator).

Author:

    Leonardo (leonardo) 2011-02-27

Notes:

--*/
#include<utility>
#include "util/stack.h"
#include "util/vector.h"

typedef std::pair<unsigned, unsigned> point;

static void tst1() {
    stack s;
    
    point * p1 = new (s) point(10, 20);
    point * p2 = new (s) point(30, 40);
    void * ptr = s.allocate(16000);
    ENSURE(p2->first == 30 && p2->second == 40);
    ENSURE(p1->first == 10 && p1->second == 20);
    s.deallocate(static_cast<int*>(ptr));
    s.deallocate(p2);
    s.deallocate(p1);
}

static void tst2(unsigned num, unsigned del_rate) {
    ptr_vector<char> ptrs;
    stack s;
    for (unsigned i = 0; i < num; i++) {
        ENSURE(ptrs.empty() == s.empty());
        ENSURE(s.empty() || ptrs.back() == s.top());
        if (!ptrs.empty() && rand() % del_rate == 0) {
            s.deallocate();
            ptrs.pop_back();
        }
        else {
            unsigned size;
            if (rand()%10 == 0) {
                size = 8192 + rand()%800;
            }
            else {
                size = rand()%100;
            }
            char * ptr = static_cast<char*>(s.allocate(size));
            ptrs.push_back(ptr);
        }
    }
    while (s.empty()) {
        ENSURE(ptrs.empty() == s.empty());
        ENSURE(s.empty() || ptrs.back() == s.top());
        s.deallocate();
        ptrs.pop_back();
    }
}

void tst_stack() {
    tst1();
    tst2(1000, 10);
    tst2(2000, 2);
    tst2(100000, 10);
    tst2(300000, 5);
    tst2(300000, 2);
    tst2(300000, 7);
}
