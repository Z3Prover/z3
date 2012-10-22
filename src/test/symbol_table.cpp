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
#include"symbol_table.h"

static void tst1() {
    symbol_table<int> t;
    t.insert(symbol("foo"), 35);
    SASSERT(t.contains(symbol("foo")));
    SASSERT(!t.contains(symbol("boo")));
    t.begin_scope();
    t.insert(symbol("boo"), 20);
    SASSERT(t.contains(symbol("boo")));
#ifdef Z3DEBUG
    int tmp;
#endif
    SASSERT(t.find(symbol("boo"), tmp) && tmp == 20);
    SASSERT(t.find(symbol("foo"), tmp) && tmp == 35);
    t.insert(symbol("foo"), 100);
    SASSERT(t.find(symbol("foo"), tmp) && tmp == 100);
    t.end_scope(); 
    SASSERT(t.find(symbol("foo"), tmp) && tmp == 35);
    SASSERT(!t.contains(symbol("boo")));
    t.reset();
    SASSERT(!t.contains(symbol("boo")));
    SASSERT(!t.contains(symbol("foo")));
}

void tst_symbol_table() {
    tst1();
}

