/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    trail.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-02-26.

Revision History:

--*/
#include"core_theory.h"

void tst_trail() {
    core_theory t;
    bvalue<int> v(10);
    t.push();
    v.set(t, 20);
    v.set(t, 30);
    SASSERT(v.get() == 30);
    t.pop(1);
    SASSERT(v.get() == 10);
    t.push();
    t.push();
    v.set(t, 100);
    SASSERT(v.get() == 100);
    t.pop(2);
    SASSERT(v.get() == 10);
    t.push();
    t.push();
    v.set(t, 40);
    SASSERT(v.get() == 40);
    t.pop(1);
    SASSERT(v.get() == 10);
}
