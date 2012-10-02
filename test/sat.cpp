/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_sat.cpp

Abstract:

    Test SAT solver

Author:

    Leonardo de Moura (leonardo) 2006-10-05.

Revision History:

--*/

#include"sat_def.h"

class sat_tester {

    static void tst1() {
        sat_solver<no_extension> solver;
        solver.push_user_scope();
        solver.push_scope();
        literal l1  = solver.mk_var();
        SASSERT(solver.m_ref_count[l1.var()] == 1);
        solver.assert_lit(l1);
        SASSERT(solver.m_ref_count[l1.var()] == 2);
        SASSERT(solver.m_weak_ref_count[l1.var()] == 1);
        SASSERT(solver.get_assignment(l1) == l_true);
        SASSERT(solver.m_level[l1.var()] == 1);
        literal l2 = solver.mk_var();
        SASSERT(solver.m_ref_count[l2.var()] == 1);
        SASSERT(solver.get_assignment(l2) == l_undef);
        SASSERT(solver.m_level.size() == 3);
        SASSERT(solver.m_free_var_indices.size() == 0);
        solver.pop_scope(1);
        SASSERT(solver.m_free_var_indices.size() == 2);
        SASSERT(solver.m_ref_count[l1.var()] == 0);
    }
    
    template<typename Ext>
    static void tst2() {
        sat_solver<Ext> solver;
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        literal l4 = solver.mk_var();
        solver.mk_aux_clause(~l1, ~l2, l3, CLS_MAIN);
        solver.mk_aux_clause(~l3, ~l4, CLS_MAIN);
        solver.push_scope();
        solver.assign(l1, mk_axiom());
        solver.assign(l2, mk_axiom());
        SASSERT(solver.get_assignment(l3) == l_undef);
        SASSERT(solver.get_assignment(l4) == l_undef);
        solver.propagate();
        SASSERT(solver.get_assignment(l3) == l_true);
        SASSERT(solver.get_assignment(l4) == l_false);
        solver.pop_scope(1);
        SASSERT(solver.get_assignment(l1) == l_undef);
        SASSERT(solver.get_assignment(l2) == l_undef);
        SASSERT(solver.get_assignment(l3) == l_undef);
        SASSERT(solver.get_assignment(l4) == l_undef);
    }

    static void tst3() {
        sat_solver<no_extension> solver;
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        solver.push_scope();
        SASSERT(solver.m_ref_count[l1.var()] == 1);
        solver.mk_aux_clause(~l1, l2, CLS_TRANSIENT);
        SASSERT(solver.m_ref_count[l1.var()] == 2);
        solver.assign(l1, mk_axiom());
        solver.propagate();
        SASSERT(solver.get_assignment(l2) == l_true);
        SASSERT(solver.m_transient_clauses.size() == 1);
        TRACE("sat_ext", tout << "ref_count: " << solver.m_ref_count[l1.var()] << ", scope_lvl: " << solver.m_scope_lvl << "\n";);
        SASSERT(solver.m_ref_count[l1.var()] == 3);
        SASSERT(solver.m_ref_count[l2.var()] == 3);
        solver.pop_scope(1);
        solver.assign(l1, mk_axiom());
        solver.propagate();
        SASSERT(solver.get_assignment(l2) == l_undef);
        SASSERT(solver.m_transient_clauses.size() == 0);
        SASSERT(solver.m_ref_count[l1.var()] == 2);
        SASSERT(solver.m_ref_count[l2.var()] == 1);
    }

    static void tst4() {
        sat_solver<no_extension> solver;
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        literal l4 = solver.mk_var();
        solver.push_user_scope();
        solver.mk_aux_clause(~l1, l2, l4, CLS_MAIN);
        solver.push_user_scope();
        solver.mk_aux_clause(~l1, ~l2, l3, CLS_MAIN);
        solver.push_scope();
        solver.mk_aux_clause(~l3, ~l4, CLS_TRANSIENT);
        solver.mk_aux_clause(~l1, ~l4, CLS_MAIN);
        SASSERT(solver.m_ref_count[l1.var()] == 4);
        SASSERT(solver.m_ref_count[l2.var()] == 3);
        SASSERT(solver.m_ref_count[l3.var()] == 3);
        SASSERT(solver.m_ref_count[l4.var()] == 4);
        SASSERT(solver.m_main_clauses.size() == 3);
        SASSERT(solver.m_transient_clauses.size() == 1);
        solver.pop_scope(2);
        SASSERT(solver.m_ref_count[l1.var()] == 2);
        SASSERT(solver.m_ref_count[l2.var()] == 2);
        SASSERT(solver.m_ref_count[l3.var()] == 1);
        SASSERT(solver.m_ref_count[l4.var()] == 2);
        SASSERT(solver.m_main_clauses.size() == 1);
        SASSERT(solver.m_transient_clauses.size() == 0);
        solver.assign(l1, mk_axiom());
        SASSERT(solver.get_assignment(l4) == l_undef);
        solver.pop_scope(1);
        SASSERT(solver.m_main_clauses.size() == 0);
        SASSERT(solver.m_ref_count[l1.var()] == 1);
        SASSERT(solver.m_ref_count[l2.var()] == 1);
        SASSERT(solver.m_ref_count[l3.var()] == 1);
        SASSERT(solver.m_ref_count[l4.var()] == 1);
    }

    template<typename Ext>
    static void tst5() {
        sat_solver<Ext> solver;
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        solver.push_scope();
        solver.assign(l1, mk_axiom());
        solver.push_scope();
        solver.mk_aux_clause(~l1, l2, CLS_MAIN);
        SASSERT(solver.get_assignment(l2) == l_true);
        solver.pop_scope(1);
        SASSERT(solver.get_assignment(l2) == l_true);
        solver.pop_scope(1);
        SASSERT(solver.get_assignment(l2) == l_undef);
        SASSERT(solver.m_main_clauses.size() == 1);
    }

    static void tst6() {
        sat_solver<no_extension> solver;
        
        literal l = solver.mk_var();
        solver.assert_lit(l);
        SASSERT(!solver.inconsistent());
        solver.push_scope();
        solver.assign(~l, mk_axiom());
        SASSERT(solver.inconsistent());
        solver.pop_scope(1);
        SASSERT(!solver.inconsistent());
    }

    class no_ref_count : public no_extension {
    public:
        static bool ref_counters_enabled() {
            return false; 
        }
    };

    static void tst7() {
        sat_solver<no_ref_count> solver;
        literal l1 = solver.mk_var();
        solver.push_user_scope();
        literal l2 = solver.mk_var();
        SASSERT(solver.get_var_vector_size() == 3);
        solver.pop_scope(1);
        SASSERT(solver.get_var_vector_size() == 2);
    }

    static void tst8() {
        literal l[2];
        l[0] = true_literal;
        l[1] = true_literal;
        clause * cls = clause::mk_clause(2, l, CLS_EXTERNAL);
        SASSERT(cls->kind() == CLS_EXTERNAL);
        dealloc(cls);
    }

    static void tst9() {
        sat_solver<no_extension> solver;

        solver.push_scope();
        literal l1 = solver.mk_var();
        literal l2 = solver.mk_var();
        literal l3 = solver.mk_var();
        solver.mk_aux_clause(l1, l2, l3, CLS_MAIN);
        solver.pop_scope(1);
        SASSERT(solver.m_ref_count[l1.var()] == 1);
        SASSERT(solver.get_assignment(l1) == l_undef);
        solver.assert_lit(~l2);
        solver.assert_lit(~l3);
        solver.propagate();
        SASSERT(solver.get_assignment(l1) == l_true);
        SASSERT(solver.m_main_clauses.size() == 1);
        SASSERT(solver.m_ref_count[l1.var()] == 2);
        solver.simplify_clauses();
        SASSERT(solver.m_main_clauses.size() == 0);
        SASSERT(solver.m_ref_count[l1.var()] == 1);
        SASSERT(solver.m_weak_ref_count[l1.var()] == 1);
        SASSERT(solver.get_assignment(l1) == l_true);
    }

    static void tst10() {
        sat_solver<no_extension> s;
        
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        literal l3 = s.mk_var();
        
        s.push_scope();
        s.assign(l1, mk_axiom());
        s.push_scope();
        literal l4 = s.mk_var();
        s.assign(l4, mk_axiom());
        s.mk_aux_clause(~l4, l3, CLS_TRANSIENT);
        s.mk_aux_clause(~l4, l2, CLS_TRANSIENT);
        s.mk_aux_clause(~l3, ~l1, ~l2, CLS_TRANSIENT);
        SASSERT(s.inconsistent());
#ifdef  Z3DEBUG
        bool r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
        SASSERT(s.m_scope_lvl == 1);
        SASSERT(s.m_ref_count[l4.var()] > 0);
        s.pop_scope(1);
        SASSERT(s.get_assignment(l1) == l_undef);
        SASSERT(s.get_assignment(l4) == l_undef);
        s.push_scope();
        s.assign(l4, mk_axiom());
#ifdef  Z3DEBUG
        s.del_learned_clauses();
#endif 
        s.pop_scope(1);
    }

    static void tst11() {
        // out-of-order conflict bug.
        sat_solver<no_extension> s;

        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        s.push_scope();
        s.assign(l1, mk_axiom());
        s.assign(l2, mk_axiom());
        s.push_scope();
        s.mk_aux_clause(~l1, ~l2, CLS_TRANSIENT);
        s.propagate();
        s.resolve_conflict();
    }

    static void tst12() {
        // out-of-order conflict bug.
        sat_solver<no_extension> s;

        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        literal l3 = s.mk_var();
        s.push_scope();
        s.assign(l1, mk_axiom());
        s.assign(l2, mk_axiom());
        s.push_scope();
        s.assign(l3, mk_axiom());
        s.mk_aux_clause(~l1, ~l2, CLS_TRANSIENT);
        s.propagate();
        s.resolve_conflict();
    }

    static void tst13() {
        sat_solver<no_extension> s;
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        literal l3 = s.mk_var();
        s.push_scope();
        s.assign(l1, mk_axiom());
        s.push_scope();
        s.assign(l2, mk_axiom());
        s.push_scope();
        s.mk_aux_clause(~l1, l3, CLS_MAIN);
        s.propagate();
        SASSERT(!s.inconsistent());
        SASSERT(s.get_assignment(l3) == l_true);
        s.mk_aux_clause(~l1, ~l2, CLS_TRANSIENT);
        s.propagate();
        SASSERT(s.inconsistent());
#ifdef Z3DEBUG
        bool r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
        SASSERT(s.get_assignment(l3) == l_true);
        TRACE("sat", tout << l3 << " : " << s.get_assignment(l3) << " : " << s.m_level[l3.var()] << " : " << s.m_scope_lvl << "\n";);
    }

    static void tst14() {
        sat_solver<no_extension> s;
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        s.push_scope();
        s.assign(~l1, mk_axiom());
        s.push_scope();
        s.assign(~l2, mk_axiom());
        s.assert_lit(l1);
        SASSERT(s.inconsistent());
#ifdef Z3DEBUG
        bool r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
        SASSERT(s.get_assignment(l1) == l_true);
    }

    static void tst15() {
        sat_solver<no_extension> s;
        literal l1 = s.mk_var();
        literal l2 = s.mk_var();
        s.push_scope();
        s.assign(~l1, mk_axiom());
        s.push_scope();
        s.assign(~l2, mk_axiom());
        s.assert_lit(l1);
        SASSERT(s.inconsistent());
#ifdef Z3DEBUG
        bool r = 
#endif
            s.resolve_conflict();
        SASSERT(r);
        SASSERT(s.get_assignment(l1) == l_true);
    }

    static void tst16() {
        sat_solver<no_extension> s;
        s.push_scope();
        literal l1 = s.mk_var();
        bool_var v1 = l1.var();
        s.inc_weak_ref(v1);
        s.pop_scope(1);
        SASSERT(s.get_ref_count(v1) == 0);
        literal l2 = s.mk_var();
        SASSERT(l2.var() != v1);
        s.dec_weak_ref(v1);
        literal l3 = s.mk_var();
        SASSERT(l3.var() == v1);
    }

public:    
    static void run_tests() {
        enable_trace("sat_ext");
        enable_trace("backtrack");
        enable_trace("mk_clause");
        enable_debug("mk_clause");
        enable_trace("propagate");
        enable_trace("simplify");
        enable_trace("del_learned_clauses");
        enable_debug("sat_invariant");
        TRACE("sat_ext", tout << "running SAT solver tests...\n";);
        tst1();
        tst2<no_extension>();
        tst2<no_ref_count>();
        tst3();
        tst4();
        tst5<no_extension>();
        tst5<no_ref_count>();
        tst6();
        tst7();
        tst8();
        tst9();
        tst10();
        tst11();
        tst12();
        tst13();
        tst14();
        tst15();
        tst16();
    }
};

void tst_sat() {
    TRACE("sat", tout << "sizeof(clause): " << sizeof(clause) << "\n";);
    sat_tester::run_tests();
}


