/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    gate.cpp

Abstract:

    Test SAT gates

Author:

    Leonardo de Moura (leonardo) 2006-11-02.

Revision History:

--*/
#include"sat_def.h"

class gate_extension : public no_extension {
public:
    bool relevancy_enabled() {
        return true;
    }

    bool gates_enabled() {
        return true;
    }
};


class gate_no_rel_extension : public no_extension {
public:
    bool relevancy_enabled() {
        return false;
    }

    bool gates_enabled() {
        return true;
    }
};

class sat_gate_tester {

    static void tst1() {
        sat_solver<gate_no_rel_extension> solver; 
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        
        SASSERT(solver.mk_or(l1, l2, l3) == solver.mk_or(l3, l1, l2));
        
        SASSERT(solver.mk_or(l1, l1, l3) == solver.mk_or(l3, l1));
    
        SASSERT(solver.mk_or(l1, l1, l1) == l1);
    
        SASSERT(solver.mk_or(l1, false_literal, l1) == l1);
        
        SASSERT(solver.mk_or(l1, true_literal, l1) == true_literal);

        solver.assert_lit(l1);

        SASSERT(solver.mk_or(l1, l2, l3) == true_literal);

        literal l4 = solver.mk_or(l2, l3);
    
        SASSERT(l4 != true_literal && l4 != false_literal);
    
        solver.push();

        solver.assert_lit(l2);
    
        solver.propagate();
    
        SASSERT(solver.get_assignment(l4) == l_true);

        solver.pop(1);

        SASSERT(solver.get_assignment(l4) == l_undef);

        solver.push();
    
        solver.assert_lit(~l2);
    
        solver.assert_lit(~l3);

        solver.propagate();

        SASSERT(solver.get_assignment(l4) == l_false);

        solver.pop(1);

        SASSERT(solver.get_assignment(l4) == l_undef);

        SASSERT(l4 == ~solver.mk_and(~l2, ~l3));
    }

    static void tst1a() {
        sat_solver<gate_extension> solver; 
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        
        SASSERT(solver.mk_or(l1, l2, l3) == solver.mk_or(l3, l1, l2));
        
        SASSERT(solver.mk_or(l1, l1, l3) == solver.mk_or(l3, l1));
    
        SASSERT(solver.mk_or(l1, l1, l1) == l1);
    
        SASSERT(solver.mk_or(l1, false_literal, l1) == l1);
        
        SASSERT(solver.mk_or(l1, true_literal, l1) == true_literal);

        solver.assert_lit(l1);

        SASSERT(solver.mk_or(l1, l2, l3) != true_literal);

        literal l4 = solver.mk_or(l2, l3);
    
        SASSERT(l4 != true_literal && l4 != false_literal);
    
        solver.push();

        solver.assert_lit(l2);
    
        solver.propagate();
    
        SASSERT(solver.get_assignment(l4) == l_true);

        solver.pop(1);

        SASSERT(solver.get_assignment(l4) == l_undef);

        solver.push();
    
        solver.assert_lit(~l2);
    
        solver.assert_lit(~l3);

        solver.propagate();

        SASSERT(solver.get_assignment(l4) == l_false);

        solver.pop(1);

        SASSERT(solver.get_assignment(l4) == l_undef);

        SASSERT(l4 == ~solver.mk_and(~l2, ~l3));
    }

    static void tst2() {
        sat_solver<gate_extension> solver; 

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();

        SASSERT(solver.mk_iff(l1, l2) == solver.mk_iff(l2, l1));

        SASSERT(solver.mk_iff(l1, true_literal) == l1);

        SASSERT(solver.mk_iff(l1, false_literal) == ~l1);

        SASSERT(solver.mk_iff(true_literal, l2) == l2);

        SASSERT(solver.mk_iff(false_literal, l2) == ~l2);

        SASSERT(solver.mk_iff(l1, l1) == true_literal);

        SASSERT(solver.mk_iff(l1, ~l1) == false_literal);
    }

    static void tst3() {
        sat_solver<gate_extension> solver; 

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();

        solver.push();

        literal l3 = solver.mk_or(l1, l2);
        SASSERT(solver.m_ref_count[l3.var()] == 1);

        solver.pop(1);
    }

    static void tst4() {
        sat_solver<gate_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();

        literal l3 = solver.mk_or(l1, l2);
        
        solver.reset();
        
        l1 = solver.mk_var();

    }

    static void tst5() {
        sat_solver<gate_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();

        solver.push_scope();

        solver.assign(l1, mk_axiom());

        solver.propagate();
        
        solver.push_scope();

        literal l4 = solver.mk_or(l1, l2);

        solver.mk_main_clause(l4, l3);

        SASSERT(solver.get_assignment(l4) == l_true);
        
        solver.pop_scope(1);

        SASSERT(solver.get_assignment(l4) == l_true);
    }

    static void tst6() {
        sat_solver<gate_no_rel_extension> solver;
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        literal l4 = solver.mk_var();

        SASSERT(solver.mk_ite(l1, l2, l3) == solver.mk_ite(~l1, l3, l2));

        SASSERT(solver.mk_ite(l1, l2, l2) == l2);

        solver.assert_lit(l1);

        solver.push_scope();

        SASSERT(solver.mk_ite(l1, l2, l3) == l2);

        SASSERT(solver.mk_ite(~l1, l2, l3) == l3);
    }

    static void tst6a() {
        sat_solver<gate_extension> solver;
        
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        literal l4 = solver.mk_var();

        SASSERT(solver.mk_ite(l1, l2, l3) == solver.mk_ite(~l1, l3, l2));

        SASSERT(solver.mk_ite(l1, l2, l2) == l2);

        solver.assert_lit(l1);

        solver.push_scope();

        SASSERT(solver.mk_ite(l1, l2, l3) != l2);

        SASSERT(solver.mk_ite(~l1, l2, l3) != l3);
    }

    static void tst7() {
        sat_solver<gate_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_uniq(l1);
        SASSERT(l1 != l2);

        solver.push();

        solver.assert_lit(l1);
        solver.propagate();

        SASSERT(solver.get_assignment(l1) == l_true);
        SASSERT(solver.get_assignment(l2) == l_true);
        
        solver.pop(1);
        solver.propagate();

        SASSERT(solver.get_assignment(l1) == l_undef);
        SASSERT(solver.get_assignment(l2) == l_undef);

        solver.assert_lit(~l1);
        solver.propagate();

        SASSERT(solver.get_assignment(l1) == l_false);
        SASSERT(solver.get_assignment(l2) == l_false);
    }

    static void tst8() {
        sat_solver<gate_extension> solver;

        literal l1 = solver.mk_var();
        literal l2 = solver.mk_uniq(l1);
        SASSERT(l1 != l2);

        solver.push_scope();

        solver.assert_lit(l1);
        solver.propagate();

        SASSERT(solver.get_assignment(l1) == l_true);
        SASSERT(solver.get_assignment(l2) == l_true);
        
        solver.pop_scope(1);
        solver.propagate();

        SASSERT(solver.get_assignment(l1) == l_true);
        SASSERT(solver.get_assignment(l2) == l_true);
    }

    static void tst9() {
        sat_solver<gate_extension> s;
        
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        literal l3 = s.mk_var();
        
        s.push_scope();
        s.assign(l1, mk_axiom());
        s.push_scope();
        literal l4 = s.mk_var();
        literal l5 = s.mk_var();
        literal l6 = s.mk_or(l4, l5);
        s.assign(l6, mk_axiom());
        s.mk_transient_clause(~l6, l3);
        s.mk_transient_clause(~l6, l2);
        s.mk_transient_clause(literal_vector(~l3, ~l1, ~l2));
        SASSERT(s.inconsistent());
#ifdef  Z3DEBUG
        bool r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
        SASSERT(s.m_scope_lvl == 1);
        SASSERT(s.m_ref_count[l4.var()] > 0);
        SASSERT(s.m_ref_count[l5.var()] > 0);
        SASSERT(s.m_ref_count[l6.var()] > 0);
        s.pop_scope(1);
        SASSERT(s.get_assignment(l1) == l_undef);
        SASSERT(s.get_assignment(l4) == l_undef);
        SASSERT(s.get_assignment(l5) == l_undef);
        SASSERT(s.get_assignment(l6) == l_undef);
        SASSERT(s.m_ref_count[l4.var()] > 0);
        SASSERT(s.m_ref_count[l5.var()] > 0);
        SASSERT(s.m_ref_count[l6.var()] > 0);
        s.push_scope();
        s.assign(~l4, mk_axiom());
        s.propagate();
#ifdef  Z3DEBUG
        s.del_learned_clauses();
#endif 
        s.pop_scope(1);
    }
    
    static void tst10() {
        sat_solver<gate_extension> s;
        
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        literal l3 = s.mk_var();
        
        s.push_scope();
        s.assign(l1, mk_axiom());
        s.push_scope();
        literal l4 = s.mk_var();
        literal l5 = s.mk_var();
        literal l6 = s.mk_iff(l4, l5);
        literal l7 = s.mk_var();
        literal l8 = s.mk_or(l6, l7);
        s.assign(l8, mk_axiom());
        s.mk_transient_clause(~l8, l3);
        s.mk_transient_clause(~l8, l2);
        s.mk_transient_clause(literal_vector(~l3, ~l1, ~l2));
        SASSERT(s.inconsistent());
#ifdef  Z3DEBUG
        bool r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
        SASSERT(s.m_scope_lvl == 1);
        s.pop_scope(1);
        SASSERT(s.m_ref_count[l4.var()] > 0);
        SASSERT(s.m_ref_count[l5.var()] > 0);
        SASSERT(s.m_ref_count[l6.var()] > 0);
        SASSERT(s.m_ref_count[l7.var()] > 0);
        SASSERT(s.m_ref_count[l8.var()] > 0);
        s.push_scope();
        s.assign(~l1, mk_axiom());
        s.push_scope();
        s.assign(l5, mk_axiom());
        s.mk_transient_clause(~l5, ~l4);
        s.propagate();
        SASSERT(s.get_assignment(l6) == l_false);
        SASSERT(s.get_assignment(l8) == l_undef);
#ifdef  Z3DEBUG
        s.del_learned_clauses();
        SASSERT(s.m_ref_count[l7.var()] == 0);
        SASSERT(s.m_ref_count[l8.var()] ==  0);
        SASSERT(s.m_ref_count[l4.var()] > 0);
        SASSERT(s.m_ref_count[l5.var()] > 0);
        SASSERT(s.m_ref_count[l6.var()] > 0);
#endif 
        s.mk_transient_clause(l6, l3);
        s.mk_transient_clause(l6, l2);
        s.mk_transient_clause(literal_vector(~l3, l1, ~l2));
        SASSERT(s.inconsistent());
#ifdef  Z3DEBUG
        r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
    }

    static void tst11() {
        sat_solver<gate_extension> s;

        literal l0 = s.mk_var();
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        
        s.push_scope();
        s.assign(~l1, mk_axiom());
        s.assign(~l2, mk_axiom());
        s.push_scope();
        literal l3 = s.mk_or(l1, l2);
        SASSERT(s.get_assignment(l3) == l_false);
        s.mk_main_clause(l0, l1, l3);
        SASSERT(s.m_ref_count[l3.var()] == 3);
        s.pop_scope(1);
        SASSERT(s.m_ref_count[l3.var()] == 2);
        SASSERT(s.get_assignment(l3) == l_false);
        s.assert_lit(l1);
        s.propagate();
        SASSERT(s.inconsistent());
    }
  
public:
    static void run_tests() {
        enable_trace("del_gate");
        enable_trace("sat_solver");
        enable_trace("gate");
        enable_trace("del_learned_clauses");
        tst1();
        tst1a();
        tst2();
        tst3();
        tst4();
        tst5();
        tst6();
        tst6a();
        tst7();
        tst8();
        tst9();
        tst10();
        tst11();
    }
};

void tst_gate() {
    sat_gate_tester::run_tests();
}
