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
#include "util/trace.h"
#include "util/debug.h"
#include "util/memory_manager.h"
#include "util/optional.h"

static void tst1() {
    optional<int> v;
    ENSURE(!v);
    ENSURE(v == false);
    v = 10;
    ENSURE(v);
    ENSURE(*v == 10);
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
    ENSURE(!v);
    v = OptFoo(10, 20);
    ENSURE(v->m_x == 10);
    ENSURE(v->m_y == 20);
    v = OptFoo(200, 300);
    ENSURE(v->m_x == 200);
    ENSURE(v->m_y == 300);
    TRACE("optional", tout << sizeof(v) << "\n";);
}

static void tst3() {
    optional<int *> v;
    ENSURE(!v);
    int x = 10;
    v = &x;
    ENSURE(v);
    ENSURE(*v == &x);
    TRACE("optional", tout << sizeof(v) << "\n";);
    ENSURE(*(*v) == 10);
}

void tst_optional() {
    tst1();
    tst2();
    tst3();
}

