/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    purify_arith_tactic.h

Abstract:

    Tactic for eliminating arithmetic operators: DIV, IDIV, MOD,
    TO_INT, and optionally (OP_IRRATIONAL_ALGEBRAIC_NUM).

    This tactic uses the simplifier for also eliminating:
    OP_SUB, OP_UMINUS, OP_POWER (optionally), OP_REM, OP_IS_INT. 
    
    Remarks:
      - The semantics of division by zero is not specified. Thus,
        uninterpreted functions are used.  An ExRCF procedure may
        treat the uninterpreted function applications as fresh
        constants.  Then, in any model produced by this procedure,
        the interpretation for division by zero must be checked.

      - POWER operator can only be handled if the second argument is a
        rational value.  The tactic has an option for preserving POWER
        operator where the second argument is an integer.

      - The semantics of (^ t (/ 1 k)) is not specified when t < 0 and
        k is even. Similarly to the division by zero case,
        uninterpreted function symbols are created.

      - The semantics of (^ t 0) is not specified if t == 0. Thus,
        uninterpreted function symbols are created.

      - TO_REAL is not really outside of the RCF language
        since it is only used for "casting".
  
      - All quantifiers must occur with positive polarity.
        The tactic snf (with skolemization disabled) is applied 
        to enforce that.
   
Author:

    Leonardo de Moura (leonardo) 2011-12-30.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_purify_arith_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("purify-arith", "eliminate unnecessary operators: -, /, div, mod, rem, is-int, to-int, ^, root-objects.", "mk_purify_arith_tactic(m, p)")
*/


