/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    propagate_ineqs_tactic.h

Abstract:

    This tactic performs the following tasks:

     - Propagate bounds using the bound_propagator.
     - Eliminate subsumed inequalities.  
       For example:
          x - y >= 3
          can be replaced with true if we know that
          x >= 3 and y <= 0
            
     - Convert inequalities of the form p <= k and p >= k into p = k,
       where p is a polynomial and k is a constant.

    This strategy assumes the input is in arith LHS mode.
    This can be achieved by using option :arith-lhs true in the
    simplifier.
     
Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#ifndef PROPAGATE_INEQS_TACTIC_H_
#define PROPAGATE_INEQS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_propagate_ineqs_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("propagate-ineqs", "propagate ineqs/bounds, remove subsumed inequalities.", "mk_propagate_ineqs_tactic(m, p)")
*/

#endif
