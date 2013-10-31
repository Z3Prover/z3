/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    optimize_objectives.cpp

Abstract:
   
    Objective optimization method.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:


    Suppose we obtain solution t1 = k1, ..., tn = kn-epsilon
    Assert:
      t1 > k1 \/ t2 > k2 \/ ... \/ tn >= kn
    If this solution is satisfiable, then for each t_i, maximize the 
    assignment and assert the new frontier.
    Claim: we don't necessarily have to freeze assignments of 
    t_i when optimizing assignment for t_j
    because the state will always satisfy the disjunction.
    If one of the k_i is unbounded, then omit a disjunction for it.
    Claim: the end result (when the constraints are no longer feasible) 
    is Pareto optimal, but convergence will probably not be as fast
    as when fixing one parameter at a time.
    E.g., a different approach is first to find a global maximal for one
    variable. Then add a method to "freeze" that variable at the extremum if it is finite.
    To do this, add lower and upper bounds for that variable using infinitesimals.
    If the variable is unbounded, then this is of course not sufficient by itself.
        
    

--*/

#ifndef _OPT_OBJECTIVE_H_
#define _OPT_OBJECTIVE_H_

#include "optimize_objectives.h"
#include "opt_solver.h"
#include "arith_decl_plugin.h"
#include "smt_context.h"

namespace opt {


    void optimize_objectives::set_cancel(bool f) {
        m_cancel = true;
    }

    void optimize_objectives::set_max(vector<inf_eps>& dst, vector<inf_eps> const& src) {
        for (unsigned i = 0; i < src.size(); ++i) {
            if (src[i] > dst[i]) {
                dst[i] = src[i];
            }
        }
    }


    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool optimize_objectives::basic_opt(app_ref_vector& objectives) {
        arith_util autil(m);
        s->reset_objectives();
        m_lower.reset();
        m_upper.reset();
        // First check_sat call to initialize theories
        lbool is_sat = s->check_sat(0, 0);
        if (is_sat != l_true) {
            return is_sat;
        }

        opt_solver::scoped_push _push(*s);
        opt_solver::toggle_objective _t(*s, true);

        for (unsigned i = 0; i < objectives.size(); ++i) {
            s->add_objective(objectives[i].get());
            m_lower.push_back(inf_eps(rational(-1),inf_rational(0)));
            m_upper.push_back(inf_eps(rational(1), inf_rational(0)));
        }
                
        while (is_sat == l_true && !m_cancel) {
            is_sat = update_lower();
        }      
        
        if (m_cancel || is_sat == l_undef) {
            return l_undef;
        }
        return l_true;        
    }

    lbool optimize_objectives::update_lower() {
        lbool is_sat = s->check_sat(0, 0); 
        set_max(m_lower, s->get_objective_values());
        IF_VERBOSE(1, 
                   for (unsigned i = 0; i < m_lower.size(); ++i) {
                       verbose_stream() << m_lower[i] << " ";
                   }
                   verbose_stream() << "\n";);
        expr_ref_vector disj(m);
        expr_ref constraint(m);
        
        for (unsigned i = 0; i < m_lower.size(); ++i) {
            inf_eps const& v = m_lower[i];
            disj.push_back(s->block_lower_bound(i, v));
        }
        constraint = m.mk_or(disj.size(), disj.c_ptr());
        s->assert_expr(constraint);
        return is_sat;
    }

    lbool optimize_objectives::update_upper() {
        return l_undef;
    }

    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    lbool optimize_objectives::operator()(opt_solver& solver, app_ref_vector& objectives, vector<inf_eps>& values) {
        s = &solver;
        lbool result = basic_opt(objectives);
        values.reset();
        values.append(m_lower);
        return result;
    }

}

#endif
