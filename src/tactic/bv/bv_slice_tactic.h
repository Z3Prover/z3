/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv_slice_tactic.h

Abstract:

    Tactic for simplifying with bit-vector slices

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_bv_slice_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("bv-slice", "simplify using bit-vector slices.", "mk_bv_slice_tactic(m, p)")
*/


