/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    eliminate_predicates_tactic.cpp

Abstract:

    eliminate_predicates_tactic.h is header-only (mk_eliminate_predicates_tactic is defined
    inline); this translation unit exists solely so its Z3_ADD_TACTIC registration (see
    tactic/tactic.h) actually gets linked into the program -- an `inline` global's
    constructor only runs if some compiled translation unit includes the header declaring it.

--*/
#include "tactic/core/eliminate_predicates_tactic.h"
