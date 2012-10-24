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
#ifndef _SAT_TACTIC_H_
#define _SAT_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_sat_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_sat_preprocessor_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
