/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    opt_lns.cpp

Abstract:

    Large neighborhood search default implementation 
    based on phase saving and assumptions

Author:

    Nikolaj Bjorner (nbjorner) 2018-3-13

Notes:

   
--*/

#include "opt/opt_lns.h"
#include "opt/opt_context.h"

namespace opt {
   
    lns::lns(context& ctx, solver* s):
        m(ctx.get_manager()),
        m_ctx(ctx),
        m_solver(s),
        m_models_trail(m)
    {}

    lns::~lns() {}

    void lns::display(std::ostream & out) const {
        for (auto const& q : m_queue) {
            out << q.m_index << ": " << q.m_assignment << "\n";
        }
    }
    
    lbool lns::operator()() {

        if (m_queue.empty()) {
            expr_ref_vector lits(m);
            m_ctx.get_lns_literals(lits);
            m_queue.push_back(queue_elem(lits));
            m_qhead = 0;
        }

        params_ref p;
        p.set_uint("sat.inprocess.max", 3);
        p.set_uint("smt.max_conflicts", 10000);
        m_solver->updt_params(p);

        while (m_qhead < m_queue.size()) {
            unsigned index = m_queue[m_qhead].m_index;            
            if (index > m_queue[m_qhead].m_assignment.size()) {
                ++m_qhead;
                continue;
            }
            IF_VERBOSE(2, verbose_stream() << "(opt.lns :queue " << m_qhead << " :index " << index << ")\n");
            
            // recalibrate state to an initial satisfying assignment
            lbool is_sat = m_solver->check_sat(m_queue[m_qhead].m_assignment);
            IF_VERBOSE(2, verbose_stream() << "(opt.lns :calibrate-status " << is_sat << ")\n");

            expr_ref lit(m_queue[m_qhead].m_assignment[index].get(), m);
            lit = mk_not(m, lit);
            expr* lits[1] = { lit };
            ++m_queue[m_qhead].m_index;
            if (!m.limit().inc()) {
                return l_undef;
            }

            // Update configuration for local search:
            // p.set_uint("sat.local_search_threads", 2);
            // p.set_uint("sat.unit_walk_threads", 1);
            
            is_sat = m_solver->check_sat(1, lits);
            IF_VERBOSE(2, verbose_stream() << "(opt.lns :status " << is_sat << ")\n");
            if (is_sat == l_true && add_assignment()) {
                return l_true;
            }
        }        
        return l_false;
    }

    bool lns::add_assignment() {
        model_ref mdl;
        m_solver->get_model(mdl);
        m_ctx.fix_model(mdl);
        expr_ref tmp(m);
        expr_ref_vector fmls(m);
        for (expr* f : m_queue[0].m_assignment) {
            mdl->eval(f, tmp);
            if (m.is_false(tmp)) {
                fmls.push_back(mk_not(m, tmp));
            }
            else {
                fmls.push_back(tmp);
            }
        }
        tmp = mk_and(fmls);
        if (m_models.contains(tmp)) {
            return false;
        }
        else {
            m_models.insert(tmp);
            m_models_trail.push_back(tmp);
            return true;
        }
    }
}

