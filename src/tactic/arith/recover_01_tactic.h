/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    recover_01_tactic.h

Abstract:

    Recover 01 variables

    Search for clauses of the form
    p  or q or  x = 0
    ~p or q or  x = k1
    p  or ~q or x = k2
    ~p or ~q or x = k1+k2

    Then, replaces 
    x with k1*y1 + k2*y2
    p with y1=1
    q with y2=1
    where y1 and y2 are fresh 01 variables

    The clauses are also removed.

Author:

    Leonardo de Moura (leonardo) 2012-02-17.

Revision History:

--*/
#ifndef RECOVER_01_TACTIC_H_
#define RECOVER_01_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_recover_01_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("recover-01", "recover 0-1 variables hidden as Boolean variables.", "mk_recover_01_tactic(m, p)")
*/

#endif
