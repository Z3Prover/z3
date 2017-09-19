/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    buffer.cpp

Abstract:

    Test buffers.

Author:

    Leonardo de Moura (leonardo) 2011-03-03.

Revision History:

--*/
#include "util/ptr_scoped_buffer.h"

typedef std::pair<int, int> point;

template class ptr_scoped_buffer<point>;

static void tst1() {
    ptr_scoped_buffer<point> b;
    ENSURE(b.empty());
    b.push_back(alloc(point, 10, 20));
    ENSURE(!b.empty());
    point * p1 = alloc(point, 30, 20); 
    b.push_back(p1);
    ENSURE(b.get(1) == p1);
    b.push_back(alloc(point, 40, 20));
    ENSURE(b.size() == 3);
    b.pop_back();
    ENSURE(b.get(0) != p1);
    ENSURE(b.get(1) == p1);
    point * p2 = alloc(point, 30, 20); 
    ENSURE(b.get(0) != p2);
    b.set(0, p2);
    ENSURE(b.get(0) == p2);
    ENSURE(b.size() == 2);
    b.push_back(alloc(point, 40, 40));
}

void tst_buffer() {
    tst1();
}
