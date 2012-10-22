/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    list.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-07-10.

Revision History:

--*/
#include"trace.h"
#include"util.h"
#include"region.h"
#include"list.h"

static void tst1() {
    region r;
    list<int> * l1 = new (r) list<int>(10);
    list<int> * l2 = new (r) list<int>(20, l1);
    list<int> * l3 = new (r) list<int>(30);
    list<int> * l4 = new (r) list<int>(40, l3);
    SASSERT(append(r, l1, static_cast<list<int> *>(0)) == l1);
    SASSERT(append(r, l2, static_cast<list<int> *>(0)) == l2);
    SASSERT(append(r, static_cast<list<int> *>(0), l2) == l2);
    SASSERT(append(r, static_cast<list<int> *>(0), static_cast<list<int> *>(0)) == 0);
    TRACE("list", display(tout, l2->begin(), l2->end()); tout << "\n";);
    list<int> * l5 = append(r, l4, l2);
    TRACE("list", display(tout, l5->begin(), l5->end()); tout << "\n";);
    list<int> * l6 = append(r, l5, l5);
    TRACE("list", display(tout, l6->begin(), l6->end()); tout << "\n";);
}

void tst_list() {
    tst1();
}

