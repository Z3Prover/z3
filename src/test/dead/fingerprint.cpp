/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    fingerprint.cpp

Abstract:

    Test fingerprint support

Author:

    Leonardo de Moura (leonardo) 2006-10-29.

Revision History:

--*/
#include"core_theory.h"

bool add_fingerprint(core_theory & t, void * data, enode * n1) {
    enode * c[1];
    c[0] = n1;
    return t.add_fingerprint(data, 1, c);
}

bool add_fingerprint(core_theory & t, void * data, enode * n1, enode * n2) {
    enode * c[2];
    c[0] = n1;
    c[1] = n2;
    return t.add_fingerprint(data, 2, c);
}

bool add_fingerprint(core_theory & t, void * data, enode * n1, enode * n2, enode * n3, enode * n4, enode * n5, enode * n6, enode * n7, enode * n8, enode * n9) {
    enode * c[9];
    c[0] = n1;
    c[1] = n2;
    c[2] = n3;
    c[3] = n4;
    c[4] = n5;
    c[5] = n6;
    c[6] = n7;
    c[7] = n8;
    c[8] = n9;
    return t.add_fingerprint(data, 9, c);
}

class fingerprint_tester {

    static void tst1() {
        core_theory t;
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        void * d1 = reinterpret_cast<void *>(1);
        
        SASSERT(add_fingerprint(t, 0, n1));
        SASSERT(!add_fingerprint(t, 0, n1));
        SASSERT(add_fingerprint(t, 0, n2));

        SASSERT(add_fingerprint(t, d1, n1));
        SASSERT(!add_fingerprint(t, d1, n1));
        SASSERT(add_fingerprint(t, d1, n2));
        SASSERT(add_fingerprint(t, d1, n1, n2));
        SASSERT(add_fingerprint(t, d1, n2, n1));
        SASSERT(!add_fingerprint(t, d1, n1, n2));
        SASSERT(!add_fingerprint(t, d1, n2, n1));
        
        t.push_scope();
        
        SASSERT(add_fingerprint(t, 0, n3));
        SASSERT(add_fingerprint(t, d1, n3));
        SASSERT(add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n2)); 
        SASSERT(!add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n2)); 
        SASSERT(add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n1)); 
        SASSERT(!add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n1)); 
        
        t.pop_scope(1);
        
        SASSERT(!add_fingerprint(t, 0, n1));
        SASSERT(!add_fingerprint(t, 0, n2));
        SASSERT(!add_fingerprint(t, d1, n1, n2));
        SASSERT(!add_fingerprint(t, d1, n2, n1));
        SASSERT(add_fingerprint(t, 0, n3));
        SASSERT(add_fingerprint(t, d1, n3));
        SASSERT(add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n2)); 
        SASSERT(!add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n2)); 
        SASSERT(add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n1)); 
        SASSERT(!add_fingerprint(t, d1, n1, n1, n1, n1, n1, n1, n2, n1, n1)); 
    }

public:
    
    static void run_tests() {
        tst1();
    }
};

void tst_fingerprint() {
    fingerprint_tester::run_tests();
}
