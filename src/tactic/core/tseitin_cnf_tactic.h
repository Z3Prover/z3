/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tseitin_cnf_tactic.h

Abstract:

    Puts an assertion set in CNF.
    Auxiliary variables are used to avoid blowup.

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#ifndef _TSEITIN_CNF_TACTIC_H_
#define _TSEITIN_CNF_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_tseitin_cnf_core_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_tseitin_cnf_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
