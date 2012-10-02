/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    distinct.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-11-03.

Revision History:

--*/
#include"core_theory.h"

class distinct_tester {
    static void tst1() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * d[3] = {n1, n2, n3};
        
        enode * n4 = t.mk_const();
        enode * n5 = t.mk_const();
        enode * n6 = t.mk_const();
        
        t.assert_distinct_class(3, d);
        TRACE("distinct", t.display(tout););
        t.propagate();

        t.push();
        
        t.assert_lit(t.mk_eq(n1, n2));
        t.propagate();
        SASSERT(t.inconsistent());
        
        t.pop(1);
        SASSERT(!t.inconsistent());
        TRACE("distinct", t.display(tout););

        t.push_scope();

        t.assign(t.mk_eq(n1, n4), mk_axiom());
        t.assign(t.mk_eq(n2, n5), mk_axiom());
        t.assign(t.mk_eq(n2, n6), mk_axiom());
        t.propagate();
        SASSERT(!t.inconsistent());

        t.assign(t.mk_eq(n4,n5), mk_axiom());
        t.propagate();
        TRACE("distinct", t.display(tout););
        SASSERT(t.inconsistent());
    }
    
    static void tst2() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        t.assert_lit(t.mk_eq(n1,n3));
        t.propagate();

        enode * d[3] = {n1, n2, n3};
        
        t.assert_distinct_class(3, d);
        SASSERT(t.inconsistent());
    }

    static void tst3() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        t.assert_lit(t.mk_eq(n1,n3));

        enode * d[3] = {n1, n2, n3};
        
        t.assert_distinct_class(3, d);
        
        t.propagate();
        SASSERT(t.inconsistent());
    }

    static void tst4() {
#ifdef ENABLE_DISTINCT_CLASSES_SUPPORT
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        
        t.push();
   
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        enode * d1[3] = {n1, n2, n3};
        
        t.assert_distinct_class(3, d1);

        SASSERT(n1->get_distinct_classes() == 1);
        SASSERT(n2->get_distinct_classes() == 1);
        SASSERT(n3->get_distinct_classes() == 1);
        
        enode * n4 = t.mk_const();
        enode * n5 = t.mk_const();
        enode * n6 = t.mk_const();

        enode * d2[3] = {n4, n5, n6};
        
        t.assert_distinct_class(3, d2);
        
        SASSERT(n4->get_distinct_classes() == 2);
        SASSERT(n5->get_distinct_classes() == 2);
        SASSERT(n6->get_distinct_classes() == 2);

        enode * n7 = t.mk_const();
        enode * n8 = t.mk_const();
        enode * n9 = t.mk_const();

        enode * d3[3] = {n7, n8, n9};
        
        t.assert_distinct_class(3, d3);
        
        SASSERT(n7->get_distinct_classes() == 4);
        SASSERT(n8->get_distinct_classes() == 4);
        SASSERT(n9->get_distinct_classes() == 4);

        enode * n10 = t.mk_const();
        enode * n11 = t.mk_const();
        enode * n12 = t.mk_const();

        enode * d4[3] = {n10, n11, n12};
        
        t.assert_distinct_class(3, d4);

        SASSERT(n10->get_distinct_classes() == 8);
        SASSERT(n11->get_distinct_classes() == 8);
        SASSERT(n12->get_distinct_classes() == 8);
        
        t.push_scope();
        
        t.assign(t.mk_eq(n7, n1), mk_axiom());
        t.propagate();
        SASSERT(!t.inconsistent());
        SASSERT(n1->get_root()->get_distinct_classes() == 5);

        t.push_scope();
        
        t.assign(t.mk_eq(n11, n5), mk_axiom());
        t.propagate();
        SASSERT(!t.inconsistent());
        SASSERT(n5->get_root()->get_distinct_classes() == 10);

        t.push_scope();
        t.assign(t.mk_eq(n7, n3), mk_axiom());
        t.propagate();
        SASSERT(t.inconsistent());

        t.pop_scope(1);
        SASSERT(!t.inconsistent());

        t.push_scope();

        t.assign(t.mk_eq(n11, n1), mk_axiom());
        t.propagate();
        SASSERT(!t.inconsistent());
        SASSERT(n1->get_root()->get_distinct_classes() == 15);

        t.pop_scope(1);
        
        SASSERT(!t.inconsistent());
        SASSERT(n1->get_root()->get_distinct_classes()  == 5);
        SASSERT(n11->get_root()->get_distinct_classes() == 10);
        SASSERT(n5->get_root()->get_distinct_classes() == 10);

        t.pop_scope(1);
        SASSERT(n1->get_root()->get_distinct_classes()  == 5);
        SASSERT(n7->get_root()->get_distinct_classes()  == 5);
        SASSERT(n11->get_root()->get_distinct_classes() == 8);
        SASSERT(n5->get_root()->get_distinct_classes()  == 2);
        
        t.pop_scope(1);
        SASSERT(n1->get_root()->get_distinct_classes()  == 1);
        SASSERT(n7->get_root()->get_distinct_classes()  == 4);
        SASSERT(n11->get_root()->get_distinct_classes() == 8);
        SASSERT(n5->get_root()->get_distinct_classes()  == 2);
        
        SASSERT(t.m_num_distinct_classes == 4);

        t.pop(1);

        SASSERT(t.m_num_distinct_classes == 0);
#endif
    }

    static void tst5() {
#ifdef ENABLE_DISTINCT_CLASSES_SUPPORT
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        
        t.push();

        enode * n1;
        enode * n2;
        enode * n3;

        for (unsigned i = 0; i < 40; i++) {
            n1 = t.mk_const();
            n2 = t.mk_const();
            n3 = t.mk_const();
            
            enode * d1[3] = {n1, n2, n3};
            
            t.assert_distinct_class(3, d1);
        }

        SASSERT(t.m_num_distinct_classes == 32);
        SASSERT(n1->get_root()->get_distinct_classes() == 0);

        t.push_scope();
        t.assign(t.mk_eq(n1, n3), mk_axiom());
        t.propagate();
        
        SASSERT(t.inconsistent());

        t.pop_scope(1);
        SASSERT(!t.inconsistent());

        t.pop(1);
        SASSERT(t.m_num_distinct_classes == 0);

        n1 = t.mk_const();
        n2 = t.mk_const();
        n3 = t.mk_const();

        enode * d1[3] = {n1, n2, n3};
        
        t.assert_distinct_class(3, d1);
        SASSERT(n1->get_root()->get_distinct_classes() == 1);
#endif
    }

    static void tst6() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;

        t.push_scope();
        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        enode * d1[3] = {n1, n2, n3};
        
        t.assert_distinct_class(3, d1);
        
        SASSERT(t.m_num_distinct_classes == 0);
        SASSERT(n1->get_root()->get_distinct_classes() == 0);

        t.assign(t.mk_eq(n1, n3), mk_axiom());
        t.propagate();
        
        SASSERT(t.inconsistent());
    }

public:
    
    static void run_tests() {
        tst1();
        tst2();
        tst3();
        tst4();
        tst5();
        tst6();
    }
};


void tst_distinct() {
    enable_trace("core_theory_conflict");
    distinct_tester::run_tests();
}

