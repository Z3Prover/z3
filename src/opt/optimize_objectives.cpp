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

namespace opt {

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool mathsat_style_opt(
        opt_solver& s, 
        app_ref_vector const& objectives, 
        vector<inf_eps_rational<inf_rational> >& values) 
    {
        ast_manager& m = objectives.get_manager();
        arith_util autil(m);

        s.reset_objectives();
        // First check_sat call to initialize theories
        lbool is_sat = s.check_sat(0, 0);
        if (is_sat == l_false) {
            return is_sat;
        }

        s.push();

        opt_solver::toggle_objective _t(s, true);

        for (unsigned i = 0; i < objectives.size(); ++i) {
            s.add_objective(objectives[i]);            
        }

        is_sat = s.check_sat(0, 0);
                
        while (is_sat == l_true) {
            // Extract values for objectives
            values.reset();
            values.append(s.get_objective_values());
            IF_VERBOSE(1, 
                       for (unsigned i = 0; i < values.size(); ++i) {
                           verbose_stream() << values[i] << " ";
                       }
                       verbose_stream() << "\n";);
            expr_ref_vector disj(m);
            expr_ref constraint(m), num(m);
            for (unsigned i = 0; i < objectives.size(); ++i) {

                if (!values[i].get_infinity().is_zero()) {
                    continue;
                }
                num = autil.mk_numeral(values[i].get_rational(), m.get_sort(objectives[i]));
                
                SASSERT(values[i].get_infinitesimal().is_nonpos());
                if (values[i].get_infinitesimal().is_neg()) {
                    disj.push_back(autil.mk_ge(objectives[i], num));
                }
                else {
                    disj.push_back(autil.mk_gt(objectives[i], num));
                }
            }
            constraint = m.mk_or(disj.size(), disj.c_ptr());
            s.assert_expr(constraint);
            is_sat = s.check_sat(0, 0);
        }      

        s.pop(1);
       
        if (is_sat == l_undef) {
            return is_sat;
        }
        return l_true;
    }

    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    
    lbool optimize_objectives(opt_solver& s, 
                          app_ref_vector& objectives, 
                          vector<inf_eps_rational<inf_rational> >& values) {
        return mathsat_style_opt(s, objectives, values);
    }
}

#endif
