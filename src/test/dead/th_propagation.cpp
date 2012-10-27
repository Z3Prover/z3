/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    th_propagation.cpp

Abstract:

    Test theory propagation.

Author:

    Leonardo de Moura (leonardo) 2006-11-07.

Revision History:

--*/
#include"core_theory.h"

class th_propagation_tester {
    static void tst1() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        
        enode * n1  = t.mk_const();
        enode * n2  = t.mk_const();
        enode * n3  = t.mk_const();
        
        literal eq1 = t.mk_eq(n1,n2);
        literal eq2 = t.mk_eq(n2,n3);
        literal eq3 = t.mk_eq(n1,n3);

        literal l1   = t.mk_lit();
        literal l2   = t.mk_lit();
        t.mk_main_clause(l1, l2, ~eq3);
        t.mk_main_clause(~l2, ~eq3);
        t.mk_main_clause(~l1, ~eq2);

        t.push_scope();
        t.assign(eq1, mk_axiom());
        t.propagate();

        t.push_scope();
        t.assign(eq2, mk_axiom());
        t.propagate();
        SASSERT(t.get_assignment(eq3) == l_true);
        SASSERT(t.inconsistent());
        bool r = t.m_sat->resolve_conflict();
        SASSERT(r);
    }

public:
    static void run_tests() {
        enable_trace("th_prop");
        enable_trace("scope");
        enable_trace("conflict");
        tst1();
    }
};

void tst_th_propagation() {
    th_propagation_tester::run_tests();
}

