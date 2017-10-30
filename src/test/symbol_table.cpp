/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_symbol_table.cpp

Abstract:

    Test symbol table module.

Author:

    Leonardo de Moura (leonardo) 2006-09-19.

Revision History:

--*/
#include "util/symbol_table.h"

static void tst1() {
    symbol_table<int> t;
    t.insert(symbol("foo"), 35);
    ENSURE(t.contains(symbol("foo")));
    ENSURE(!t.contains(symbol("boo")));
    t.begin_scope();
    t.insert(symbol("boo"), 20);
    ENSURE(t.contains(symbol("boo")));
    int tmp;
    ENSURE(t.find(symbol("boo"), tmp) && tmp == 20);
    ENSURE(t.find(symbol("foo"), tmp) && tmp == 35);
    t.insert(symbol("foo"), 100);
    ENSURE(t.find(symbol("foo"), tmp) && tmp == 100);
    t.end_scope(); 
    ENSURE(t.find(symbol("foo"), tmp) && tmp == 35);
    ENSURE(!t.contains(symbol("boo")));
    t.reset();
    ENSURE(!t.contains(symbol("boo")));
    ENSURE(!t.contains(symbol("foo")));
}

void tst_symbol_table() {
    tst1();
}

