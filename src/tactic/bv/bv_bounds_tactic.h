/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv_bounds_tactic.h

Abstract:

    Contextual bounds simplification tactic.

Author:

    Nuno Lopes (nlopes) 2016-2-12
    Nikolaj Bjorner (nbjorner)


--*/
#pragma once
#include "tactic/tactic.h"

tactic * mk_bv_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_dom_bv_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("propagate-bv-bounds", "propagate bit-vector bounds by simplifying implied or contradictory bounds.", "mk_bv_bounds_tactic(m, p)")


  ADD_TACTIC("propagate-bv-bounds-new", "propagate bit-vector bounds by simplifying implied or contradictory bounds.", "mk_dom_bv_bounds_tactic(m, p)")


*/

