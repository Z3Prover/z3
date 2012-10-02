/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    diff_neq_tactic.h

Abstract:

    Solver for integer problems that contains literals of the form
       k <= x
       x <= k
       x - y != k
    And all variables are bounded.   

Author:

    Leonardo de Moura (leonardo) 2012-02-07.

Revision History:

--*/
#ifndef _DIFF_NEQ_TACTIC_H_
#define _DIFF_NEQ_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_diff_neq_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
