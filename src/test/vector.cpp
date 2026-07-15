/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_vector.cpp

Abstract:

    Test my vector template.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#include "util/vector.h"
#include "util/rational.h"
#include <iostream>

static void tst_resize_rational() {
    // grow from empty using default initialization (zero)
    vector<rational> v;
    v.resize(4);
    ENSURE(v.size() == 4);
    for (unsigned i = 0; i < 4; ++i)
        ENSURE(v[i].is_zero());

    // shrink: elements below new size are preserved
    v.resize(2);
    ENSURE(v.size() == 2);
    for (unsigned i = 0; i < 2; ++i)
        ENSURE(v[i].is_zero());

    // grow with explicit value initialization
    rational half(1, 2);
    v.resize(6, half);
    ENSURE(v.size() == 6);
    for (unsigned i = 0; i < 2; ++i)
        ENSURE(v[i].is_zero());
    for (unsigned i = 2; i < 6; ++i)
        ENSURE(v[i] == half);

    // resize to same size is a no-op
    rational three(3);
    v.resize(6, three);
    ENSURE(v.size() == 6);
    for (unsigned i = 2; i < 6; ++i)
        ENSURE(v[i] == half);

    // resize to zero clears the vector
    v.resize(0);
    ENSURE(v.empty());

    // grow again after being empty
    rational neg(-7);
    v.resize(3, neg);
    ENSURE(v.size() == 3);
    for (unsigned i = 0; i < 3; ++i)
        ENSURE(v[i] == neg);
}

static void tst_resize() {
    // grow from empty using default initialization
    svector<int> v;
    v.resize(5);
    ENSURE(v.size() == 5);
    ENSURE(v.capacity() >= 5);
    for (unsigned i = 0; i < 5; ++i)
        ENSURE(v[i] == 0);

    // shrink: elements below new size are preserved, size shrinks
    v.resize(3);
    ENSURE(v.size() == 3);
    for (unsigned i = 0; i < 3; ++i)
        ENSURE(v[i] == 0);

    // grow with explicit value initialization
    v.resize(7, 42);
    ENSURE(v.size() == 7);
    for (unsigned i = 0; i < 3; ++i)
        ENSURE(v[i] == 0);
    for (unsigned i = 3; i < 7; ++i)
        ENSURE(v[i] == 42);

    // resize to same size is a no-op
    v.resize(7, 99);
    ENSURE(v.size() == 7);
    for (unsigned i = 3; i < 7; ++i)
        ENSURE(v[i] == 42);

    // resize to zero clears the vector
    v.resize(0);
    ENSURE(v.empty());
    ENSURE(v.size() == 0);

    // grow again after being empty
    v.resize(4, 10);
    ENSURE(v.size() == 4);
    for (unsigned i = 0; i < 4; ++i)
        ENSURE(v[i] == 10);
}

static void tst1() {
    svector<int> v1;
    ENSURE(v1.empty());
    for (unsigned i = 0; i < 1000; ++i) {
        v1.push_back(i + 3);
        ENSURE(static_cast<unsigned>(v1[i]) == i + 3);
        ENSURE(v1.capacity() >= v1.size());
        ENSURE(!v1.empty());
    }
    for (unsigned i = 0; i < 1000; ++i) {
        ENSURE(static_cast<unsigned>(v1[i]) == i + 3);
    }
    svector<int>::iterator it = v1.begin();
    svector<int>::iterator end = v1.end();
    for (int i = 0; it != end; ++it, ++i) {
        ENSURE(*it == i + 3);
    }
    for (unsigned i = 0; i < 1000; ++i) {
        ENSURE(static_cast<unsigned>(v1.back()) == 1000 - i - 1 + 3);
        ENSURE(v1.size() == 1000 - i);
        v1.pop_back();
    }
    ENSURE(v1.empty());
    ENSURE(v1.empty());
    unsigned i = 1000000000;
    while (true) {
        std::cout << "resize " << i << "\n";
        try {            
            v1.resize(i);
        }
        catch (z3_exception& e) {
            std::cout << e.what() << "\n";
            break;
        }
        i *= 2;
    }
}

void tst_vector() {
    tst_resize_rational();
    tst_resize();
    tst1();
}
