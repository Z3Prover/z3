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
    lbool mathsat_style_opt(opt_solver& s, 
                          expr_ref_vector& objectives, svector<bool> const& is_max,
                          vector<inf_eps_rational<rational> >& values) {
        enable_trace("maximize");        
        // First check_sat call for initialize theories
        lbool is_sat = s.check_sat(0, 0);
        if (is_sat == l_false) {
            return l_false;
        }

        s.push();

        // Assume there is only one objective function
        ast_manager& m = objectives.get_manager();
        arith_util autil(m);
        app* objective = m.mk_fresh_const("objective", autil.mk_real());
        if (is_max[0]) {
	        s.assert_expr(autil.mk_eq(objective, objectives[0].get()));
        } else {
	        s.assert_expr(autil.mk_eq(objective, autil.mk_uminus(objectives[0].get())));
        };
        s.set_objective(objective);
        s.toggle_objective(true);
        is_sat = s.check_sat(0, 0);        
        
        while (is_sat != l_false) {
            // Extract values for objectives
            inf_eps_rational<rational> val;
			val = is_max[0] ? s.get_objective_value() : -s.get_objective_value();

            // Check whether objective is unbounded
            if (!val.is_rational()) {
                values.reset();
                values.push_back(val);
                break;
            }
            
            // If values have initial data, they will be dropped
            values.reset();
            values.push_back(val);
            
            // Assert there must be something better            
            expr_ref_vector assumptions(m);
            expr* bound = m.mk_fresh_const("bound", m.mk_bool_sort());
            assumptions.push_back(bound);
            expr* r = autil.mk_numeral(val.get_rational(), false);
            s.assert_expr(m.mk_eq(bound, is_max[0] ? autil.mk_gt(objectives[0].get(), r) : autil.mk_lt(objectives[0].get(), r)));
            is_sat = s.check_sat(1, assumptions.c_ptr());            
        }      

        s.pop(1);
                
        return l_true;
    }

    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    
    lbool optimize_objectives(opt_solver& s, 
                          expr_ref_vector& objectives, svector<bool> const& is_max,
                          vector<inf_eps_rational<rational> >& values) {
        return mathsat_style_opt(s, objectives, is_max, values);
    }
}

#endif
