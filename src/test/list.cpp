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
#include "util/trace.h"
#include "util/util.h"
#include "util/region.h"
#include "util/list.h"
#include "util/id_var_list.h"

#include <limits>

static void tst1() {
    region r;
    list<int> * l1 = new (r) list<int>(10);
    list<int> * l2 = new (r) list<int>(20, l1);
    list<int> * l3 = new (r) list<int>(30);
    list<int> * l4 = new (r) list<int>(40, l3);
    ENSURE(append(r, l1, static_cast<list<int> *>(nullptr)) == l1);
    ENSURE(append(r, l2, static_cast<list<int> *>(nullptr)) == l2);
    ENSURE(append(r, static_cast<list<int> *>(nullptr), l2) == l2);
    ENSURE(append(r, static_cast<list<int> *>(nullptr), static_cast<list<int> *>(nullptr)) == nullptr);
    TRACE(list, display(tout, l2->begin(), l2->end()); tout << "\n";);
    list<int> * l5 = append(r, l4, l2);
    TRACE(list, display(tout, l5->begin(), l5->end()); tout << "\n";);
    list<int> * l6 = append(r, l5, l5);
    (void) l6;
    TRACE(list, display(tout, l6->begin(), l6->end()); tout << "\n";);
}

static void tst_id_var_list() {
    region r;
    for (int v : { (1 << 23) - 1, 1 << 23, (1 << 23) + 1, std::numeric_limits<int>::max() }) {
        id_var_list<> l(0, v);
        ENSURE(l.get_var() == v);
        ENSURE(l.find(0) == v);

        l.set_var(0);
        l.set_var(v);
        ENSURE(l.get_var() == v);

        l.del_var(0);
        ENSURE(l.empty());
        ENSURE(l.find(0) == -1);

        l.add_var(v, 0, r);
        l.add_var(v, 1, r);
        ENSURE(l.size() == 2);
        ENSURE(l.find(0) == v);
        ENSURE(l.find(1) == v);

        l.replace(0, 0);
        l.replace(v, 0);
        l.replace(0, 1);
        l.replace(v, 1);
        ENSURE(l.find(0) == v);
        ENSURE(l.find(1) == v);

        l.del_var(0);
        ENSURE(l.size() == 1);
        ENSURE(l.get_id() == 1);
        ENSURE(l.get_var() == v);
        l.del_var(1);
        ENSURE(l.empty());
    }
}

void tst_list() {
    tst1();
    tst_id_var_list();
}
