/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    relevancy.cpp

Abstract:

    Test relevancy propagation.

Author:

    Leonardo de Moura (leonardo) 2006-11-03.

Revision History:

--*/
#include"sat_def.h"

class relevancy_extension : public no_extension {
public:
    bool relevancy_enabled() {
        return true;
    }

    bool gates_enabled() {
        return true;
    }
};

class sat_relevancy_tester {

    static void tst1() {
        sat_solver<relevancy_extension> solver; 
        
        literal l1 = solver.mk_var();

        SASSERT(!solver.is_relevant(l1.var()));
        
        solver.assert_lit(l1);
        
        SASSERT(solver.is_relevant(l1.var()));
    }

    static void tst2() {
        sat_solver<relevancy_extension> solver; 
        
        literal l1 = solver.mk_var();
        
        solver.push_scope();
        
        SASSERT(!solver.is_relevant(l1.var()));

        solver.assert_lit(l1);

        SASSERT(solver.is_relevant(l1.var()));
        
        solver.pop_scope(1);

        SASSERT(solver.is_relevant(l1.var()));
    }

    static void tst3() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();

        literal l4 = solver.mk_ite(l1, l2, l3);
        solver.propagate();
        
        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));
        
        solver.mark_as_relevant(l4.var());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));

        solver.push_scope();

        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));

        solver.pop_scope(1);
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));
        
        solver.assign(~l1, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));
    }

    static void tst4() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        literal l4 = solver.mk_ite(l1, l2, l3);
        solver.propagate();

        solver.push_scope();

        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));
        
        solver.mark_as_relevant(l4.var());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));

        solver.pop_scope(1);
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));

        solver.assign(~l1, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));
        
        solver.mark_as_relevant(l4.var());
        solver.propagate();
        
        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));
    }

    static void tst5() {
        sat_solver<relevancy_extension> solver;
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();

        solver.push_scope();

        solver.assign(l1, mk_axiom());
        solver.propagate();

        literal l4 = solver.mk_ite(l1, l2, l3);

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));

        solver.mark_as_relevant(l4.var());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));
    }

    static void tst6() {
        sat_solver<relevancy_extension> solver;
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_iff(l1, l2);

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));

        solver.push_scope();

        solver.mark_as_relevant(l3.var());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        
        solver.pop_scope(1);
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));

        solver.push_scope();
        
        solver.mark_as_relevant(l2.var());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));

        solver.pop_scope(1);

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
    }

    static void tst7() {
        sat_solver<relevancy_extension> solver;
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_or(l1, l2);
        
        solver.push_scope();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));

        solver.mark_as_relevant(l3.var());
        solver.assign(l3, mk_axiom());
        solver.assign(l2, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        
        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.pop_scope(1);
        solver.propagate();
        solver.push_scope();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));

        solver.mark_as_relevant(l3.var());
        solver.assign(l3, mk_axiom());
        solver.propagate();
        
        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        
        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.assign(l2, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.pop_scope(1);
        solver.propagate();
        solver.push_scope();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        
        solver.assign(~l3, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        
        solver.mark_as_relevant(l3.var());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.pop_scope(1);
        solver.propagate();
        solver.push_scope();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));

        solver.mark_as_relevant(l3.var());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.assign(~l3, mk_axiom());
        solver.propagate();
        
        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
    }

    static void tst8() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_or(l1, l2);
        
        solver.push_scope();

        solver.mark_as_relevant(l3.var());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.assign(l2, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));

        solver.pop_scope(1);
        solver.propagate();
        
        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
    }

    static void tst9() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_or(l1, l2);
        
        solver.mark_as_relevant(l3.var());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        
        solver.assign(l1, mk_axiom());
        solver.assign(l2, mk_axiom());
        solver.propagate();
        
        SASSERT(solver.is_relevant(l1) || solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l1) != solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
    }

    static void tst10() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_or(l1, l2);
        
        solver.assign(l1, mk_axiom());
        solver.assign(l2, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        
        solver.mark_as_relevant(l3.var());
        solver.propagate();
        
        SASSERT(solver.is_relevant(l1) || solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l1) != solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
    }

    static void tst11() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_iff(l1, l2);
        literal l4 = solver.mk_var();
        literal l5 = solver.mk_or(l3, l4);

        solver.propagate();
        solver.push_scope();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));
        SASSERT(!solver.is_relevant(l5));

        solver.assign(l3, mk_axiom());
        solver.mark_as_relevant(l5.var());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.is_relevant(l2));
        SASSERT(solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));
        SASSERT(solver.is_relevant(l5));

        solver.assign(l4, mk_axiom());
        solver.propagate();
        SASSERT(!solver.is_relevant(l4));

        solver.pop_scope(1);
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(!solver.is_relevant(l4));
        SASSERT(!solver.is_relevant(l5));

        solver.assign(l4, mk_axiom());
        solver.mark_as_relevant(l5.var());
        solver.propagate();
        
        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));
        SASSERT(solver.is_relevant(l5));
        
        solver.assign(l1, mk_axiom());
        solver.assign(l2, mk_axiom());
        solver.assign(l3, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        SASSERT(!solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l4));
        SASSERT(solver.is_relevant(l5));
    }

    static void tst12(clause_kind k) {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        
        solver.mk_aux_clause(l1, l2, k);

        solver.push_scope();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));

        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));

        solver.assign(l2, mk_axiom());
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
        
        solver.pop_scope(1);

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
    }

    static void tst13(clause_kind k) {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        
        solver.mk_aux_clause(l1, l2, k);

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));

        solver.assign(l1, mk_axiom());
        solver.assign(l2, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));
        SASSERT(!solver.is_relevant(l2));
    }

    static void tst14() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();

        solver.push_scope();
        
        solver.assign(l1, mk_axiom());

        solver.mk_aux_clause(l1, l2, CLS_MAIN);
        solver.propagate();
        
        SASSERT(solver.is_relevant(l1));
    }

    static void tst15() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();

        solver.push_scope();
        
        solver.assign(l1, mk_axiom());
        solver.propagate();

        SASSERT(!solver.is_relevant(l1));

        solver.push_scope();

        solver.mk_aux_clause(l1, l2, CLS_MAIN);
        solver.propagate();
        
        SASSERT(solver.is_relevant(l1));
        
        solver.pop_scope(1);
        solver.propagate();

        SASSERT(solver.is_relevant(l1));
    }

    static void tst16() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();

        solver.push_scope();
        solver.assert_lit(l1);
        solver.propagate();
        SASSERT(solver.is_relevant(l1));
        SASSERT(solver.get_assignment(l1) == l_true);
        solver.assert_lit(l1);
        solver.pop_scope(1);
        SASSERT(solver.get_assignment(l1) == l_true);
        SASSERT(solver.is_relevant(l1));
    }

    static void tst17() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        solver.assert_nonrelevant_lit(l1);
        solver.mk_aux_clause(l1, l2, CLS_MAIN);
        solver.check();
        SASSERT(solver.get_assignment(l1) == l_true || solver.get_assignment(l2) == l_true);
        SASSERT(solver.is_relevant(l1) || solver.is_relevant(l2));
    }

    static void tst18() {
        sat_solver<relevancy_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        solver.assert_nonrelevant_lit(l1);
        literal l3 = solver.mk_or(l1, l2);
        SASSERT(l3 != true_literal);
        solver.assert_lit(l3);
        lbool r = solver.check();
        SASSERT(r == l_true);
        SASSERT(solver.is_relevant(l3));
        SASSERT(solver.is_relevant(l1));
    }

public:

    static void run_tests() {
        tst1();
        tst2();
        tst3();
        tst4();
        tst5();
        tst6();
        tst7();
        tst8();
        tst9();
        tst10();
        tst11();
        tst12(CLS_MAIN);
        tst12(CLS_TRANSIENT);
        tst13(CLS_AUXILIARY);
        tst13(CLS_EXT_LEMMA);
        tst13(CLS_EXTERNAL);
        tst14();
        tst15();
        tst16();
        tst17();
        tst18();
    }

};

void tst_relevancy() {
    sat_relevancy_tester::run_tests();
}
