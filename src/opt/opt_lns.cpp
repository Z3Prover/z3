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
        m_models_trail(m),
        m_atoms(m)
    {}

    lns::~lns() {}

    void lns::display(std::ostream & out) const {
        for (auto const& q : m_queue) {
            out << q.m_index << ": " << q.m_assignment << "\n";
        }
    }
    
    lbool lns::operator()() {

        if (m_queue.empty()) {
            expr_ref_vector lits(m), atoms(m);
            m_ctx.get_lns_literals(lits);
            for (expr* l : lits) {
                expr* nl = nullptr;
                if (m.is_not(l, nl)) {
                    m_atoms.push_back(nl);
                }
                else {
                    atoms.push_back(l);
                    m_atoms.push_back(l);
                }
            }
            m_queue.push_back(queue_elem(atoms));
            m_qhead = 0;
        }

        params_ref p;
        p.set_uint("sat.inprocess.max", 3);
        p.set_uint("smt.max_conflicts", 10000);
        m_solver->updt_params(p);

        while (m_qhead < m_queue.size()) {
            obj_hashtable<expr> atoms;
            for (expr* f : m_queue[m_qhead].m_assignment) {
                atoms.insert(f);
            }
            unsigned& index = m_queue[m_qhead].m_index;
            expr* lit = nullptr;
            for (; index < m_atoms.size() && (lit = m_atoms[index].get(), (atoms.contains(lit) || m_units.contains(lit))); ++index) ;
            if (index == m_atoms.size()) {
                m_qhead++;
                continue;
            }
                    
            IF_VERBOSE(2, verbose_stream() << "(opt.lns :queue " << m_qhead << " :index " << index << ")\n");
            
            // recalibrate state to an initial satisfying assignment
            lbool is_sat = m_solver->check_sat(m_queue[m_qhead].m_assignment);
            IF_VERBOSE(2, verbose_stream() << "(opt.lns :calibrate-status " << is_sat << ")\n");
            if (!m.limit().inc()) {
                return l_undef;
            }
            
            expr* lit = m_atoms[index].get();
            expr_ref_vector lits(m);
            lits.push_back(lit);
            ++index;

            // Update configuration for local search:
            // p.set_uint("sat.local_search_threads", 2);
            // p.set_uint("sat.unit_walk_threads", 1);
            
            is_sat = m_solver->check_sat(lits);
            IF_VERBOSE(2, verbose_stream() << "(opt.lns :lookahead-status " << is_sat << " " << lit << ")\n");
            if (is_sat == l_true && add_assignment()) {
                return l_true;
            }
            if (is_sat == l_false) {
                m_units.insert(lit);
            }
            if (!m.limit().inc()) {
                return l_undef;
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
        for (expr* f : m_atoms) {
            mdl->eval(f, tmp);
            if (m.is_true(tmp)) {
                fmls.push_back(f);
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

