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
#include "math/lp/lp_utils.h"
#include "ast/dl_decl_plugin.h"
#include <optional>
#include <unordered_map>

static void tst1() {
    std::optional<int> v;
    ENSURE(!v.has_value());
    v = 10;
    ENSURE(v);
    ENSURE(*v == 10);
    TRACE(optional, tout << sizeof(v) << "\n";);
}

struct OptFoo {
    int m_x;
    int m_y;

    OptFoo(int x, int y):m_x(x), m_y(y) {
    TRACE(optional, tout << "OptFoo created: " << m_x << " : " << m_y << "\n";);
    }

    ~OptFoo() {
    TRACE(optional, tout << "OptFoo deleted: " << m_x << " : " << m_y << "\n";);
    }
};

static void tst2() {
    std::optional<OptFoo> v;
    ENSURE(!v);
    v = OptFoo(10, 20);
    ENSURE(v->m_x == 10);
    ENSURE(v->m_y == 20);
    v = OptFoo(200, 300);
    ENSURE(v->m_x == 200);
    ENSURE(v->m_y == 300);
    TRACE(optional, tout << sizeof(v) << "\n";);
}

static void tst3() {
    std::optional<int *> v;
    ENSURE(!v);
    int x = 10;
    v = &x;
    ENSURE(v);
    ENSURE(*v == &x);
    TRACE(optional, tout << sizeof(v) << "\n";);
    ENSURE(*(*v) == 10);
}

static void tst_try_get_value() {
    std::unordered_map<int, std::string> map;
    map[1] = "one";
    map[2] = "two";
    map[3] = "three";
    
    // Test successful retrieval
    auto result1 = try_get_value(map, 1);
    ENSURE(result1.has_value());
    ENSURE(*result1 == "one");
    
    auto result2 = try_get_value(map, 2);
    ENSURE(result2.has_value());
    ENSURE(*result2 == "two");
    
    // Test unsuccessful retrieval
    auto result_missing = try_get_value(map, 999);
    ENSURE(!result_missing.has_value());
    
    TRACE(optional, tout << "try_get_value tests passed\n";);
}

void tst_optional() {
    tst1();
    tst2();
    tst3();
    tst_try_get_value();
}

