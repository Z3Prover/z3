/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    weighted_maxsat.h

Abstract:

    Weighted MAXSAT module

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

    Takes solver with hard constraints added.
    Returns a maximal satisfying subset of weighted soft_constraints
    that are still consistent with the solver state.

--*/
#ifndef _OPT_WEIGHTED_MAX_SAT_H_
#define _OPT_WEIGHTED_MAX_SAT_H_

#include "opt_solver.h"
#include "maxsmt.h"

namespace opt {

    maxsmt_solver_base* mk_bcd2(ast_manager& m, opt_solver* s, params_ref& p, 
                                vector<rational> const& ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_maxhs(ast_manager& m, opt_solver* s, params_ref& p, 
                                 vector<rational> const& ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_pbmax(ast_manager& m, opt_solver* s, params_ref& p, 
                                 vector<rational> const& ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_wpm2(ast_manager& m, opt_solver* s, params_ref& p,
                                vector<rational> const& ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_sls(ast_manager& m, opt_solver* s, params_ref& p,
                               vector<rational> const& ws, expr_ref_vector const& soft);

    maxsmt_solver_base* mk_wmax(ast_manager& m, opt_solver* s, params_ref& p,
                                vector<rational> const& ws, expr_ref_vector const& soft);
    
};

#endif
