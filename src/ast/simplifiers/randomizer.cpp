/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    randomizer.cpp

Abstract:

    randomizer.h is header-only (randomizer_simplifier is defined inline); this translation
    unit exists solely so its Z3_ADD_SIMPLIFIER registration (see
    ast/simplifiers/dependent_expr_state.h) actually gets linked into the program -- an
    `inline` global's constructor only runs if some compiled translation unit includes the
    header declaring it.

--*/
#include "ast/simplifiers/randomizer.h"
