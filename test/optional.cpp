/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_optional.cpp

Abstract:

    Test optional module

Author:

    Leonardo de Moura (leonardo) 2006-09-29.

Revision History:

--*/
#include"trace.h"
#include"debug.h"
#include"optional.h"

static void tst1() {
    optional<int> v;
    SASSERT(!v);
    SASSERT(v == false);
    v = 10;
    SASSERT(v);
    SASSERT(*v == 10);
    TRACE("optional", tout << sizeof(v) << "\n";);
}

struct OptFoo {
    int m_x;
    int m_y;

    OptFoo(int x, int y):m_x(x), m_y(y) {
	TRACE("optional", tout << "OptFoo created: " << m_x << " : " << m_y << "\n";);
    }

    ~OptFoo() {
	TRACE("optional", tout << "OptFoo deleted: " << m_x << " : " << m_y << "\n";);
    }
};

static void tst2() {
    optional<OptFoo> v;
    SASSERT(!v);
    v = OptFoo(10, 20);
    SASSERT(v->m_x == 10);
    SASSERT(v->m_y == 20);
    v = OptFoo(200, 300);
    SASSERT(v->m_x == 200);
    SASSERT(v->m_y == 300);
    TRACE("optional", tout << sizeof(v) << "\n";);
}

static void tst3() {
    optional<int *> v;
    SASSERT(!v);
    int x = 10;
    v = &x;
    SASSERT(v);
    SASSERT(*v == &x);
    TRACE("optional", tout << sizeof(v) << "\n";);
    SASSERT(*(*v) == 10);
}

void tst_optional() {
    tst1();
    tst2();
    tst3();
}

