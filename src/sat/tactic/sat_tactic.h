/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_tactic.cpp

Abstract:

    Tactic for using the SAT solver and its preprocessing capabilities.
    
Author:

    Leonardo (leonardo) 2011-10-26

Notes:

--*/
#ifndef SAT_TACTIC_H_
#define SAT_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_sat_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_sat_preprocessor_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC('sat', '(try to) solve goal using a SAT solver.', 'mk_sat_tactic(m, p)')
  ADD_TACTIC('sat-preprocess', 'Apply SAT solver preprocessing procedures (bounded resolution, Boolean constant propagation, 2-SAT, subsumption, subsumption resolution).', 'mk_sat_preprocessor_tactic(m, p)')
*/

#endif
