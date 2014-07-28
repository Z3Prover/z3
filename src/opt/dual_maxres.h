/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    dual_maxsres.h

Abstract:
   
    MaxRes (weighted) max-sat algorithm 
    based on dual refinement of bounds.

Author:

    Nikolaj Bjorner (nbjorner) 2014-27-7

Notes:

--*/

#ifndef _DUAL_MAXRES_H_
#define _DUAL_MAXRES_H_

namespace opt {
    maxsmt_solver_base* mk_dual_maxres(
        ast_manager& m, opt_solver* s, params_ref& p, 
        vector<rational> const& ws, expr_ref_vector const& soft);


};

#endif
