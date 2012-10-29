/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    core_theory.cpp

Abstract:

    Test core theory

Author:

    Leonardo de Moura (leonardo) 2006-10-20.

Revision History:

--*/
#include"core_theory.h"
#include"theory_diff_logic.h"

class core_theory_tester {
    static void tst1() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        enode * n1 = t.mk_const();
        SASSERT(n1->check_invariant());
        enode * n2 = t.mk_const();
        SASSERT(n2->check_invariant());
        enode * app1 = t.mk_app_core(1, n1, n2);
        enode * app2 = t.mk_app_core(1, n2, n2);
        enode * app3 = t.mk_app_core(1, n1, n2);
        SASSERT(app1 != app2);
        SASSERT(app1 == app3);

        literal l1 = t.mk_eq(n1, n2);
        literal l2 = t.mk_eq(n2, n1);
        literal l4 = t.mk_eq(n2, app1);
        SASSERT(l1 == l2);
        SASSERT(l1 != l4);

        SASSERT(n1->get_root() != n2->get_root());

        t.assert_lit(l1);
        t.assert_lit(l4);
        t.propagate();

        SASSERT(n1->get_root() == n2->get_root());
        TRACE("core_theory", t.display(tout););
    }

    static void tst2() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        enode * a1 = t.mk_app_core(1, n1, n2);

        literal l1 = t.mk_eq(n1, n2);
        t.assert_lit(l1);
        t.propagate();

        t.push_scope();
        
        literal l2 = t.mk_eq(n1, n3);
        t.assign(l2, mk_axiom());

        enode * a2 = t.mk_app_core(1, n1, n1);
        enode * a3 = t.mk_app_core(1, n1, n3);

        TRACE("core_theory", t.display(tout););

        t.propagate();
        SASSERT(t.is_equal(a1, a2));
        SASSERT(!t.is_equal(a1, a3));
        t.m_sat->mark_as_relevant(l2.var());
        t.propagate();
        SASSERT(t.is_equal(a1, a2));
        SASSERT(t.is_equal(a1, a3));

        t.pop_scope(1);

        t.propagate();
        SASSERT(to_app(a1)->get_cg() == a1);
        TRACE("core_theory", t.display(tout););
    }

    static void tst3() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        enode * a1 = t.mk_app_core(1, n1, n2);

        literal l1 = t.mk_eq(n1, n2);
        t.assert_lit(l1);
        t.propagate();

        t.push_scope();
        
        literal l2 = t.mk_eq(n1, n3);
        t.assign(l2, mk_axiom());

        enode * a2 = t.mk_app_core(1, n1, n1);
        enode * a3 = t.mk_app_core(1, n1, n3);

        TRACE("core_theory", t.display(tout););

        t.propagate();
        SASSERT(t.is_equal(a1, a2));
        SASSERT(t.is_equal(a1, a3));

        t.pop_scope(1);

        t.propagate();
        SASSERT(to_app(a1)->get_cg() == a1);
        TRACE("core_theory", t.display(tout););
    }

    static void tst8() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_const();
        enode * n5 = t.mk_const();
        enode * n6 = t.mk_const();
        
        t.push_scope();

        t.assert_lit(~t.mk_eq(n1, n2));
        t.assert_lit(t.mk_eq(n1, n3));
        t.assert_lit(t.mk_eq(n2, n4));
        t.assert_lit(t.mk_eq(n3, n6));
        t.assert_lit(t.mk_eq(n1, n5));
        t.propagate();
        
        SASSERT(!t.inconsistent());

        t.assert_lit(t.mk_eq(n3, n4));
        TRACE("core_theory", t.display(tout););
        t.propagate();

        SASSERT(t.inconsistent());

        t.pop_scope(1);
    }

    static void tst9() {
        TRACE("core_theory", tout << "tst9\n";);
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        t.push_scope();
        enode * n   = t.mk_const();
        unsigned id = n->get_id();
        t.pop_scope(1);
        TRACE("core_theory", tout << "after pop\n";);
        n = t.mk_const();
        SASSERT(id == n->get_id());
        TRACE("core_theory", tout << "end of tst9\n";);
    }

    static void tst10() {
        TRACE("core_theory", tout << "tst10\n";);
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        t.push_scope();
        enode * n   = t.mk_const();
        unsigned id = n->get_id();
        t.inc_weak_ref(id);
        t.pop_scope(1);
        TRACE("core_theory", tout << "after pop\n";);
        n = t.mk_const();
        SASSERT(id + 1 == n->get_id());
        t.dec_weak_ref(id);
        n = t.mk_const();
        SASSERT(id = n->get_id());
        TRACE("core_theory", tout << "end of tst10\n";);
    }

    static void tst11() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        t.add_eq(n1, n2, proto_eq_proof::mk_axiom());
        enode * f1 = t.mk_app_core(1, n1);
        enode * f2 = t.mk_app_core(1, n2);
        t.propagate();
        SASSERT(t.is_equal(f1, f2));
        t.push_scope();
        literal l1 = t.mk_lit();
        literal l2 = t.mk_eq(f1, f2);
        t.mk_main_clause(l1, l2);
        SASSERT(t.get_assignment(l2) == l_true);
        t.pop_scope(1);
        SASSERT(t.get_assignment(l2) == l_true);
    }

    static void tst12() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        t.add_diseq(n1, n2, proto_diseq_proof::mk_axiom());
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_const();
        t.add_eq(n1, n3, proto_eq_proof::mk_axiom());
        t.add_eq(n2, n4, proto_eq_proof::mk_axiom());
        t.propagate();
        SASSERT(t.is_diseq(n3, n4));
        t.push_scope();
        literal l1 = t.mk_lit();
        literal l2 = t.mk_eq(n3, n4);
        t.mk_main_clause(l1, l2);
        SASSERT(t.get_assignment(l2) == l_false);
        t.pop_scope(1);
        SASSERT(t.get_assignment(l2) == l_false);
    }

    static void tst13() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;
        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_app_core(1, n1);
        enode * n5 = t.mk_app_core(1, n4);
        enode * n6 = t.mk_app_core(1, n3);
        enode * n7 = t.mk_app_core(1, n6);
        
        SASSERT(!t.is_relevant(n1));
        SASSERT(!t.is_relevant(n2));        
        SASSERT(!t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));

        t.add_eq(n6, n1, proto_eq_proof::mk_axiom());

        SASSERT(!t.is_relevant(n1));
        SASSERT(!t.is_relevant(n2));        
        SASSERT(!t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));

        t.push_scope();

        t.assert_lit(t.mk_eq(n7,n2));
        t.propagate();
        SASSERT(t.is_equal(n7, n2));

        SASSERT(t.is_relevant(n1));
        SASSERT(t.is_relevant(n2));        
        SASSERT(t.is_relevant(n3));
        SASSERT(t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(t.is_relevant(n6));        
        SASSERT(t.is_relevant(n7));

        t.pop_scope(1);

        SASSERT(!t.is_relevant(n1));
        SASSERT(!t.is_relevant(n2));        
        SASSERT(!t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));
    }

    static void tst14() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 2;
        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_app_core(1, n1);
        enode * n5 = t.mk_app_core(1, n4);
        enode * n6 = t.mk_app_core(1, n3);
        enode * n7 = t.mk_app_core(1, n6);

        t.assert_lit(t.mk_eq(n1,n2));
        t.propagate();

        SASSERT(t.is_relevant(n1));
        SASSERT(t.is_relevant(n2));        
        SASSERT(!t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));

        t.push_scope();
        t.assign_eq(n2, n3, proto_eq_proof::mk_axiom());
        t.propagate();

        SASSERT(t.is_relevant(n1));
        SASSERT(t.is_relevant(n2));        
        SASSERT(t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));

        t.pop_scope(1);
        
        SASSERT(t.is_relevant(n1));
        SASSERT(t.is_relevant(n2));        
        SASSERT(!t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));

        t.push_scope();
        t.assign_eq(n2, n7, proto_eq_proof::mk_axiom());
        t.propagate();

        SASSERT(t.is_relevant(n1));
        SASSERT(t.is_relevant(n2));        
        SASSERT(t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(t.is_relevant(n6));        
        SASSERT(t.is_relevant(n7));
        
        t.pop_scope(1);

        SASSERT(t.is_relevant(n1));
        SASSERT(t.is_relevant(n2));        
        SASSERT(!t.is_relevant(n3));
        SASSERT(!t.is_relevant(n4));        
        SASSERT(!t.is_relevant(n5));
        SASSERT(!t.is_relevant(n6));        
        SASSERT(!t.is_relevant(n7));
    }

    static void tst15() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
  
        literal l1 = t.mk_lit();
        literal l2 = t.mk_lit();
        literal l3 = t.mk_lit();
        literal l4 = t.mk_lit();
        
        t.push_scope();
        t.assign(l1, mk_axiom());
        t.push_scope();

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * a1 = t.mk_app_core(1, n1);
        enode * a2 = t.mk_app_core(1, n2);
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_const();

        literal eq1 = t.mk_eq(a1, n3);
        t.assign(eq1, mk_axiom());

        t.push_scope();
        literal eq2 = t.mk_eq(a2, n4);
        t.assign(eq2, mk_axiom());

        TRACE("core_theory", tout << "eq1: " << eq1 << ", eq2: " << eq2 << "\n";);

        t.mk_transient_clause(~eq2, l3);
        t.mk_transient_clause(~eq2, l4);
        t.mk_transient_clause(~eq1, l2);
        literal_vector lits;
        lits.push_back(~l4); lits.push_back(~l3); lits.push_back(~l2); lits.push_back(~l1);
        t.mk_transient_clause(lits);
        SASSERT(t.inconsistent());
#ifdef  Z3DEBUG
        bool r = 
#endif
            t.m_sat->resolve_conflict();
        SASSERT(r);
        SASSERT(t.m_sat->m_scope_lvl == 2);
        SASSERT(t.m_sat->m_ref_count[eq1.var()] > 0);
        SASSERT(t.m_sat->m_ref_count[eq2.var()] > 0);
        t.pop_scope(2);
        SASSERT(n1->get_ref_count() > 0);
        SASSERT(n2->get_ref_count() > 0);
        SASSERT(a1->get_ref_count() > 0);
        SASSERT(a2->get_ref_count() > 0);
        t.push_scope();
        literal eq3 = t.mk_eq(n1, n2);
        t.assign(eq3, mk_axiom());
        t.propagate();
        TRACE("core_theory", t.display(tout););
        SASSERT(a1->get_root() == a2->get_root());
#ifdef  Z3DEBUG
        t.m_sat->del_learned_clauses();
#endif 
        t.pop_scope(1);
    }

    static void tst16(bool use_relevancy) {
        core_theory t;
        t.m_params.m_relevancy_lvl = use_relevancy ? 2 : 0;

        literal l0 = t.mk_lit();
        literal l1 = t.mk_lit();
        literal l2 = t.mk_lit();
        literal l3 = t.mk_lit();
        literal l4 = t.mk_lit();

        
        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_app_core(1, n1);
        
        t.push_scope();
        t.assign(l0, mk_axiom());
        
        t.push_scope();
        t.assign(l1, mk_axiom());

        t.push_scope();
        enode * n5 = t.mk_app_core(1, n2);
        enode * n6 = t.mk_const();
        literal eq1 = t.mk_eq(n5, n6);
        t.assign(eq1, mk_axiom());
        t.mk_transient_clause(~l1,  l2);
        t.mk_transient_clause(~eq1, l3);
        t.mk_transient_clause(~eq1, l4);
        literal_vector lits;
        lits.push_back(~l4); lits.push_back(~l3); lits.push_back(~l2); 
        t.mk_transient_clause(lits);
        SASSERT(t.inconsistent());
#ifdef  Z3DEBUG
        bool r = 
#endif
            t.m_sat->resolve_conflict();
        SASSERT(r);
        t.propagate();
        SASSERT(t.m_sat->m_scope_lvl == 2);
        SASSERT(t.m_sat->m_ref_count[eq1.var()] > 0);
        SASSERT(t.m_sat->get_assignment(eq1) == l_false);
        
        t.pop_scope(1);
        SASSERT(t.m_sat->m_scope_lvl == 1);
        SASSERT(t.m_sat->m_ref_count[eq1.var()] > 0);
        SASSERT(t.m_sat->get_assignment(eq1) == l_undef);

        t.push_scope();
        SASSERT(n5->get_ref_count() == 1);
        t.add_eq(n1, n2, proto_eq_proof::mk_axiom());
        SASSERT(to_app(n4)->get_cg() == n5);
        if (use_relevancy) {
            t.mark_as_relevant(n5);
        }
        SASSERT(!use_relevancy || n5->get_ref_count() == 3);
        SASSERT(use_relevancy || n5->get_ref_count() == 2);
        SASSERT(n5->get_root() != n4->get_root());
        SASSERT(!use_relevancy || t.is_relevant(n5));
        t.propagate();
        SASSERT(n5->get_root() == n4->get_root());
        SASSERT(!use_relevancy || n5->get_ref_count() == 4);
        SASSERT(use_relevancy || n5->get_ref_count() == 3);
#ifdef  Z3DEBUG
        t.m_sat->del_learned_clauses();
#endif 
        SASSERT(!use_relevancy || n5->get_ref_count() == 3);
        SASSERT(use_relevancy || n5->get_ref_count() == 2);

        SASSERT(t.m_sat->m_ref_count[eq1.var()] == 0);

        t.pop_scope(1);
    }

    static void tst17() {
        theory_idl idl;
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;

        t.add_theory(&idl);

        literal l0 = t.mk_lit();
        literal l1 = t.mk_lit();
        literal l2 = t.mk_lit();
        literal l3 = t.mk_lit();
        literal l4 = t.mk_lit();
        enode * n1 = t.mk_const();

        t.push_scope();
        t.assign(l0, mk_axiom());
        
        t.push_scope();
        t.assign(l1, mk_axiom());

        t.push_scope();
        enode * n2 = idl.mk_offset(n1, rational(1));
        enode * n3 = t.mk_const();
        literal eq1 = t.mk_eq(n2, n3);
        t.assign(eq1, mk_axiom());
        t.mk_transient_clause(~l1,  l2);
        t.mk_transient_clause(~eq1, l3);
        t.mk_transient_clause(~eq1, l4);
        literal_vector lits;
        lits.push_back(~l4); lits.push_back(~l3); lits.push_back(~l2); 
        t.mk_transient_clause(lits);
        SASSERT(t.inconsistent());
#ifdef  Z3DEBUG
        bool r = 
#endif
            t.m_sat->resolve_conflict();
        SASSERT(r);
        t.propagate();
        SASSERT(t.m_sat->m_scope_lvl == 2);
        SASSERT(t.m_sat->m_ref_count[eq1.var()] > 0);
        SASSERT(t.m_sat->get_assignment(eq1) == l_false);

        t.pop_scope(1);
        SASSERT(t.m_sat->m_scope_lvl == 1);
        SASSERT(t.m_sat->m_ref_count[eq1.var()] > 0);
        SASSERT(t.m_sat->get_assignment(eq1) == l_undef);
        SASSERT(n2->get_ref_count() == 1);
        unsigned n2_id = n2->get_id();

        // n2 is still alive
#ifdef  Z3DEBUG
        t.m_sat->del_learned_clauses();
#endif 
        // n2 is dead
        SASSERT(t.m_enodes[n2_id] == 0);
        // n2_id cannot be reused since its weak_counter > 0
        // SASSERT(t.m_weak_counters[n2_id] > 0);

        enode * n4 = idl.mk_offset(n1, rational(1)); 
        SASSERT(n4->get_id() != n2_id);
        SASSERT(n4->get_id() < static_cast<unsigned>(t.m_next_id));
   }

    static void tst18() {
        core_theory t;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        enode * a1 = t.mk_app_core(1, n1, n2);

        literal l1 = t.mk_eq(n1, n3);
        t.assert_lit(l1);
        t.propagate();

        enode * args[2] = { n3, n2 };

        SASSERT(t.get_enode_eq_to_app(1, 2, args) != 0);
        SASSERT(a1->get_root() == t.get_enode_eq_to_app(1, 2, args)->get_root());
    }

    static void tst19() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();

        literal l1 = t.mk_eq(n1, n2);
        literal l2 = t.mk_eq(n2, n3);
        literal l3 = t.mk_eq(n1, n3);
        
        enode * n4 = t.mk_const();
        enode * n5 = t.mk_const();
        enode * n6 = t.mk_const();
        enode * n7 = t.mk_const();
        
        literal l4 = t.mk_eq(n4, n5);
        literal l5 = t.mk_eq(n6, n7);
        literal l6 = t.mk_eq(n5, n7);
        literal l7 = t.mk_eq(n4, n6);
        
        t.mk_main_clause(l3, l7);

        t.push_scope();
        t.assign(l1, mk_axiom());
        t.assign(~l2, mk_axiom());
        t.assign(l4, mk_axiom());
        t.assign(l5, mk_axiom());
        t.assign(~l6, mk_axiom());
        t.propagate();
        SASSERT(t.inconsistent());
        t.m_sat->resolve_conflict();
    }

    static void tst20() {
        theory_idl idl;
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;

        t.add_theory(&idl);
        
        enode * n1 = t.mk_const();
        enode * n2 = idl.mk_offset(n1, rational(1));
        enode * n3 = idl.mk_offset(n2, rational(1));
        enode * n4 = idl.mk_offset(n1, rational(2));
        SASSERT(n4 == n3);

        enode * r1 = idl.mk_num(rational(1));
        enode * r2 = idl.mk_offset(r1, rational(1));
        enode * r3 = idl.mk_num(rational(2));
        SASSERT(r2 == r3);
    }

    static void tst21() {
        enable_debug("add_eq");
        enable_debug("core_invariant");
        theory_idl idl;
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        t.add_theory(&idl);
        theory_id  idl_id = idl.get_id();

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_const();
        enode * n5 = t.mk_const();
        literal l1 = t.mk_eq(n1, n2);
        literal l2 = t.mk_eq(n1, n3);
        literal l3 = t.mk_eq(n4, n5);
        literal l4 = t.mk_eq(n4, n3);

        t.push_scope();
        t.assign(l1, mk_axiom());
        t.propagate();
        SASSERT(n2->get_root() == n2);
        t.push_scope();
        t.assign(l2, mk_axiom());
        t.propagate();
        t.push_scope();
        t.assign(l3, mk_axiom());
        t.propagate();
        SASSERT(n5->get_root() == n5);
        SASSERT(n4->get_root() == n5);
        t.push_scope();
        t.assign(l4, mk_axiom());
        t.propagate();
        SASSERT(n2->get_root() == n2);
        enode * o1 = idl.mk_offset(n4, rational(1));
        SASSERT(n4->get_th_var(idl_id) != null_theory_var);
        SASSERT(n2->get_th_var(idl_id) == n4->get_th_var(idl_id));
        t.pop_scope(1);
        SASSERT(n4->get_th_var(idl_id) != null_theory_var);
        SASSERT(n5->get_th_var(idl_id) == n4->get_th_var(idl_id));
        SASSERT(n2->get_th_var(idl_id) == null_theory_var);
        t.pop_scope(1);
        SASSERT(n4->get_th_var(idl.get_id()) != null_theory_var);
        SASSERT(n5->get_th_var(idl_id) == null_theory_var);
        SASSERT(n2->get_th_var(idl_id) == null_theory_var);
    }

    static void tst22() {
        enable_debug("add_eq");
        enable_debug("core_invariant");
        theory_idl idl;
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        t.add_theory(&idl);
        theory_id  idl_id = idl.get_id();

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_const();
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_const();
        enode * n5 = t.mk_const();
        enode * o1 = idl.mk_offset(n2, rational(1));
        literal l1 = t.mk_eq(n1, n2);
        literal l2 = t.mk_eq(n1, n3);
        literal l3 = t.mk_eq(n4, n5);
        literal l4 = t.mk_eq(n4, n3);
        
        t.push_scope();
        t.assign(l1, mk_axiom());
        t.propagate();
        SASSERT(n2->get_root() == n2);
       
        t.push_scope();
        t.assign(l2, mk_axiom());
        t.propagate();

        t.push_scope();
        t.assign(l3, mk_axiom());
        t.propagate();
        SASSERT(n5->get_root() == n5);
        SASSERT(n4->get_root() == n5);
         
        t.push_scope();
        t.assign(l4, mk_axiom());
        t.propagate();
        SASSERT(n2->get_root() == n2);
        enode * o2 = idl.mk_offset(n4, rational(1));
        SASSERT(n4->get_th_var(idl_id) != null_theory_var);
        SASSERT(n2->get_th_var(idl_id) != null_theory_var);
        SASSERT(n2->get_th_var(idl_id) != n4->get_th_var(idl_id));
        
        t.pop_scope(1);
        SASSERT(n2->get_th_var(idl_id) != null_theory_var);
        SASSERT(n4->get_th_var(idl_id) != null_theory_var);
        SASSERT(n4->get_th_var(idl_id) == n5->get_th_var(idl_id));
        
        t.pop_scope(1);
        SASSERT(n2->get_th_var(idl_id) != null_theory_var);
        SASSERT(n4->get_th_var(idl_id) != null_theory_var);
        SASSERT(n5->get_th_var(idl_id) == null_theory_var);
    }

    static void tst23() {
        core_theory t;
        t.m_params.m_relevancy_lvl = 0;
        enable_trace("th_diseq_prop_bug");
        enable_trace("add_eq");

        enode * n1 = t.mk_const();
        enode * n2 = t.mk_true_term();
        enode * d[2] = {n1, n2};
        t.assert_distinct_class(2, d);
        enode * n3 = t.mk_const();
        enode * n4 = t.mk_const();
        
        literal l1 = t.mk_eq(n3, n4);
        literal l2 = t.mk_eq(n4, n1);
        literal l3 = t.mk_eq(n3, n2);
        t.push_scope();
        t.assign(l1, mk_axiom());
        t.propagate();
        SASSERT(n3->get_root() == n4->get_root());
        t.push_scope();
        t.assign(l2, mk_axiom());
        t.propagate();
        SASSERT(n3->get_root() == n1->get_root());
        SASSERT(t.is_diseq(n3, n2));
        SASSERT(t.get_assignment(l3) == l_false);
        SASSERT(t.m_sat->m_explanation[l3.var()].kind() == EXPL_EXT);
        literal_vector antecedents;
        t.get_antecedents(~l3, t.m_sat->m_explanation[l3.var()].obj(), antecedents);
    }

public:
    static void run_tests() {
        tst1();
        tst2();
        tst3();
        tst8();
        tst9();
        tst10();
        tst11();
        tst12();
        tst13();
        tst14();
        tst15();
        tst16(false);
        tst16(true);
        tst17();
        tst18();
        tst19();
        tst20();
        tst21();
        tst22();
        tst23();
    }
};

struct foo {
    bool_var  m_var;        // boolean variable associated with the equation
    enode *   m_lhs;
    enode *   m_rhs;
};

struct bar {
    bool m_v1:1;
    bool m_v2:1;
    bool m_v3:1;
    bool m_v4:1;
    bool m_v5:1;
    bool m_v6:1;
    bool m_v7:1;
    bool m_v8:1;
};

struct bar2 {
    bool     m_v1:1;
    bool     m_v2:1;
    unsigned m_val:30;
};

void tst_core_theory() {
    TRACE("core_theory", tout << "sizeof(equation): " << sizeof(equation) << "\n";);
    TRACE("core_theory", tout << "sizeof(foo):  " << sizeof(foo) << "\n";);
    TRACE("core_theory", tout << "sizeof(bar):  " << sizeof(bar) << "\n";);
    TRACE("core_theory", tout << "sizeof(bar2): " << sizeof(bar2) << "\n";);
    TRACE("core_theory", tout << "sizeof(theory_var_list): " << sizeof(theory_var_list) << "\n";);
    TRACE("core_theory", tout << "sizeof(enode): " << sizeof(enode) << "\n";);
    enable_debug("cg_bug");
    core_theory_tester::run_tests();
}

