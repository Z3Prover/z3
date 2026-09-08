/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_slice_tactic.cpp

Abstract:

    bv_slice_tactic.h is header-only (mk_bv_slice_tactic is defined inline); this translation
    unit exists solely so its Z3_ADD_TACTIC/Z3_ADD_SIMPLIFIER registrations (see
    tactic/tactic.h, ast/simplifiers/dependent_expr_state.h) actually get linked into the
    program -- an `inline` global's constructor only runs if some compiled translation unit
    includes the header declaring it.

--*/
#include "tactic/bv/bv_slice_tactic.h"
