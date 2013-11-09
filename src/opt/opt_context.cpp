/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.cpp

Abstract:

    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/

#include "opt_context.h"
#include "ast_pp.h"
#include "opt_solver.h"
#include "opt_params.hpp"

namespace opt {

    context::context(ast_manager& m):
        m(m),
        m_hard_constraints(m),
        m_optsmt(m)
    {
        m_params.set_bool("model", true);
        m_params.set_bool("unsat_core", true);
        m_solver = alloc(opt_solver, m, m_params, symbol());
    }

    context::~context() {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
    }

    void context::add_soft_constraint(expr* f, rational const& w, symbol const& id) { 
        maxsmt* ms;
        if (!m_maxsmts.find(id, ms)) {
            ms = alloc(maxsmt, m);
            m_maxsmts.insert(id, ms);
        }
        ms->add(f, w);
    }

    lbool context::optimize() {
        // TBD: add configuration parameter to select between box and pareto
        return optimize_box();
    }

    lbool context::optimize_box() {
        opt_solver& s = *m_solver.get(); 
        solver::scoped_push _sp(s);

        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s.assert_expr(m_hard_constraints[i].get());
        }
                
        lbool is_sat = l_true;
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; is_sat == l_true && it != end; ++it) {
            maxsmt* ms = it->m_value;
            is_sat = (*ms)(s);
        }
        if (is_sat == l_true) {           
            is_sat = m_optsmt(s);
        }
        return is_sat;
    }

    // finds a random pareto front.
    // enumerating more is TBD, e.g., 
    lbool context::optimize_pareto() {
        opt_solver& s = *m_solver.get(); 
        opt_solver::scoped_push _sp(s);

        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s.assert_expr(m_hard_constraints[i].get());
        }
                
        lbool is_sat = l_true;
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; is_sat == l_true && it != end; ++it) {
            maxsmt* ms = it->m_value;
            is_sat = (*ms)(s);
            ms->commit_assignment();            
        }
        for (unsigned i = 0; is_sat == l_true && i < m_optsmt.get_num_objectives(); ++i) {
            is_sat = m_optsmt(s);
            m_optsmt.commit_assignment(i);
        }
        return is_sat;
    }

    void context::display_assignment(std::ostream& out) {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            maxsmt* ms = it->m_value;
            if (it->m_key != symbol::null) {
                out << it->m_key << " : ";
            }
            out << ms->get_value() << "\n";
        }
        m_optsmt.display_assignment(out);
    }

    void context::display_range_assignment(std::ostream& out) {
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            maxsmt* ms = it->m_value;
            if (it->m_key != symbol::null) {
                out << it->m_key << " : ";
            }
            out << "[" << ms->get_lower() << ":" << ms->get_upper() << "]\n";
        }
        m_optsmt.display_range_assignment(out);
    }
        
    void context::set_cancel(bool f) {
        if (m_solver) {
            m_solver->set_cancel(f);
        }
        m_optsmt.set_cancel(f);
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            it->m_value->set_cancel(f);
        }
    }

    void context::collect_statistics(statistics& stats) const {
        if (m_solver) {
            m_solver->collect_statistics(stats);
        }
    }

    void context::collect_param_descrs(param_descrs & r) {
        opt_params::collect_param_descrs(r);
    }
    
    void context::updt_params(params_ref& p) {
        m_params.append(p);
        if (m_solver) {
            m_solver->updt_params(m_params);
        }
        m_optsmt.updt_params(m_params);
        map_t::iterator it = m_maxsmts.begin(), end = m_maxsmts.end();
        for (; it != end; ++it) {
            it->m_value->updt_params(m_params);
        }
    }


}
