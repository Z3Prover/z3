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
#include"vector.h"

static void tst1() {
    svector<int> v1;
    SASSERT(v1.empty());
    for (unsigned i = 0; i < 1000; i++) {
        v1.push_back(i + 3);
        SASSERT(static_cast<unsigned>(v1[i]) == i + 3);
        SASSERT(v1.capacity() >= v1.size());
        SASSERT(!v1.empty());
    }
    for (unsigned i = 0; i < 1000; i++) {
        SASSERT(static_cast<unsigned>(v1[i]) == i + 3);
    }
    svector<int>::iterator it = v1.begin();
    svector<int>::iterator end = v1.end();
    for (int i = 0; it != end; ++it, ++i) {
        SASSERT(*it == i + 3);
    }
    for (unsigned i = 0; i < 1000; i++) {
        SASSERT(static_cast<unsigned>(v1.back()) == 1000 - i - 1 + 3);
        SASSERT(v1.size() == 1000 - i);
        v1.pop_back();
    }
    SASSERT(v1.empty());
    SASSERT(v1.size() == 0);
    unsigned i = 1000000000;
    while (true) {
        std::cout << "resize " << i << "\n";
        try {            
            v1.resize(i);
        }
        catch (z3_exception& e) {
            std::cout << e.msg() << "\n";
            break;
        }
        i *= 2;
    }
}

void tst_vector() {
    tst1();
}
