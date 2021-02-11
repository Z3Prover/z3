/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    recfun_solver.cpp

Abstract:

    Recursive function solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2021-02-09

--*/

#include "sat/smt/recfun_solver.h"
#include "sat/smt/euf_solver.h"



namespace recfun {


    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("recfun"), ctx.get_manager().mk_family_id("recfun")),
        m_plugin(*reinterpret_cast<recfun::decl::plugin*>(m.get_plugin(ctx.get_manager().mk_family_id("recfun")))),
        m_util(m_plugin.u()), 
        m_disabled_guards(m),
        m_enabled_guards(m),
        m_preds(m),
        m_num_rounds(0),
        m_q_case_expand(), 
        m_q_body_expand() {
        m_num_rounds = 0;
    }    

    solver::~solver() {
        reset();
    }

    void solver::reset() {
        reset_queues();   
        m_stats.reset();
        m_disabled_guards.reset();
        m_enabled_guards.reset();
        m_q_guards.reset();
        for (auto & kv : m_guard2pending) 
            dealloc(kv.m_value);
        m_guard2pending.reset();
    }

    void solver::reset_queues() {
        for (auto* e : m_q_case_expand) {
            dealloc(e);
        }
        m_q_case_expand.reset();
        for (auto* e : m_q_body_expand) {
            dealloc(e);
        }
        m_q_body_expand.reset();
        m_q_clauses.clear();        
    }

    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) {

    }

    void solver::asserted(sat::literal l) {

    }

    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }

    void solver::collect_statistics(statistics& st) const {

    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return nullptr;
    }

    bool solver::unit_propagate() {
        return false;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) {
        return sat::null_literal;
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        return euf::null_theory_var;
    }

    void solver::init_search() {

    }
    
    void solver::finalize_model(model& mdl) {
        
    }


    
}
