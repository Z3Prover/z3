/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster_tactic.h

Abstract:

    Apply bit-blasting to a given goal.

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#ifndef _BIT_BLASTER_TACTIC_H_
#define _BIT_BLASTER_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_bit_blaster_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("bit-blast", "reduce bit-vector expressions into SAT.", "mk_bit_blaster_tactic(m, p)")
*/
#endif
