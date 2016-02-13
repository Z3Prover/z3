/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv_bounds_tactic.h

Abstract:

    Contextual bounds simplification tactic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-2-12


--*/
#ifndef BV_BOUNDS_TACTIC_H_
#define BV_BOUNDS_TACTIC_H_
#include "tactic.h"

tactic * mk_bv_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("propagate-bv-bounds", "propagate bit-vector bounds by simplifying implied or contradictory bounds.", "mk_bv_bounds_tactic(m, p)")
*/

#endif
