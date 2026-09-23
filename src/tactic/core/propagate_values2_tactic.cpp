/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    propagate_values2_tactic.cpp

Abstract:

    propagate_values2_tactic.h is header-only (mk_propagate_values2_tactic is defined inline);
    this translation unit exists solely so its Z3_ADD_TACTIC/Z3_ADD_SIMPLIFIER registrations
    (see tactic/tactic.h, ast/simplifiers/dependent_expr_state.h) actually get linked into
    the program -- an `inline` global's constructor only runs if some compiled translation
    unit includes the header declaring it.

--*/
#include "tactic/core/propagate_values2_tactic.h"
