/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    optimize_objectives.cpp

Abstract:
   
    Objective optimization method.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

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
        app_ref_vector& objectives, 
        svector<bool> const& is_max,
        vector<inf_eps_rational<rational> >& values) 
    {
        SASSERT(is_max.size() == objectives.size());

        enable_trace("maximize");        // NSB review: OK for now for debugging. Otherwise, use command-line /tr:maximize

        // First check_sat call for initialize theories
        lbool is_sat = s.check_sat(0, 0);
        if (is_sat != l_false) {
            return is_sat;
        }

        s.push();


        // Assume there is only one objective function
        SASSERT(is_max.size() == 1);
        ast_manager& m = objectives.get_manager();
        arith_util autil(m);
        bool ismax = is_max[0];
        app_ref objective_var(m), objective_term(m), obj_eq(m);
        objective_term = ismax?objectives[0].get():autil.mk_uminus(objectives[0].get());
        sort* srt = m.get_sort(objective_term);
        objective_var = m.mk_fresh_const("objective", srt);
        obj_eq = autil.mk_eq(objective_var, objective_term);
        s.assert_expr(obj_eq);
        s.set_objective(objective_var);  // NSB review: I would change signature of set_objective to take is_max and decide whether to add equation.
                                         // Otherwise, the difference logic backends will not work.
        s.toggle_objective(true);
        is_sat = s.check_sat(0, 0);        
                
        while (is_sat == l_true) {
            // Extract values for objectives
            inf_eps_rational<rational> val;
            val = is_max[0] ? s.get_objective_value() : -s.get_objective_value();

            // Check whether objective is unbounded
            // NSB: review: what if optimal is 1-epsilon. Then the check also fails.

            values.reset();
            values.push_back(val);

            if (!val.is_rational()) {
                break;
            }
 
            expr_ref constraint(m);                       
            constraint = autil.mk_gt(objective_term, autil.mk_numeral(val.get_rational(), srt));
            s.assert_expr(constraint);
            is_sat = s.check_sat(0, 0);
        }      

        s.pop(1);
       
        if (is_sat == l_undef) {
            return is_sat;
        }
        SASSERT(is_sat == l_false); // NSB review: not really water-tight with cancellation and with infinitesimal solutions.
        return l_true;
    }

    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    
    lbool optimize_objectives(opt_solver& s, 
                          app_ref_vector& objectives, svector<bool> const& is_max,
                          vector<inf_eps_rational<rational> >& values) {
        return mathsat_style_opt(s, objectives, is_max, values);
    }
}

#endif
