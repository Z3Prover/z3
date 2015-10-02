/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bv_size_reduction.h

Abstract:

    Reduce the number of bits used to encode constants, by using signed bounds.
    Example: suppose x is a bit-vector of size 8, and we have
    signed bounds for x such that:
        -2 <= x <= 2
    Then, x can be replaced by  ((sign-extend 5) k)
    where k is a fresh bit-vector constant of size 3.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#ifndef BV_SIZE_REDUCTION_TACTIC_H_
#define BV_SIZE_REDUCTION_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_bv_size_reduction_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("reduce-bv-size", "try to reduce bit-vector sizes using inequalities.", "mk_bv_size_reduction_tactic(m, p)")
*/

#endif
