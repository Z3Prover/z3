/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    optimize_objectives.h

Abstract:
   
    Objective optimization method.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/
#ifndef _OPT_OBJECTIVES_H_
#define _OPT_OBJECTIVES_H_

#include "opt_solver.h"

namespace opt {
    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    
    lbool optimize_objectives(opt_solver& s, 
                              app_ref_vector& objectives, svector<bool> const& is_max,
                              vector<inf_eps_rational<rational> >& values);
};

#endif
