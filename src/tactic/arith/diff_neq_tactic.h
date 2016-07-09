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
#ifndef DIFF_NEQ_TACTIC_H_
#define DIFF_NEQ_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_diff_neq_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("diff-neq", "specialized solver for integer arithmetic problems that contain only atoms of the form (<= k x) (<= x k) and (not (= (- x y) k)), where x and y are constants and k is a numeral, and all constants are bounded.", "mk_diff_neq_tactic(m, p)")
*/
#endif
