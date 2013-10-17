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


#include "optimize_objectives.h"

namespace opt {

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool mathsat_style_opt(solver& s, 
                          expr_ref_vector& objectives, svector<bool> const& is_max,
                          vector<optional<rational> >& values) {
        lbool is_sat;
        is_sat = s.check_sat(0,0);
        if (is_sat != l_true) {
            return is_sat;
        }
        // assume that s is instrumented to produce locally optimal assignments.

        while (is_sat != l_false) {
            model_ref model;
            s.get_model(model);
            // extract values for objectives.
            // store them in values.
            // assert there must be something better.
            is_sat = s.check_sat(0,0);
        }
        return l_true;

    }

    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    
    lbool optimize_objectives(solver& s, 
                          expr_ref_vector& objectives, svector<bool> const& is_max,
                          vector<optional<rational> >& values) {
        return mathsat_style_opt(s, objectives, is_max, values);
    }
}
