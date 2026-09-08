/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    dom_simplify_tactic.cpp

Abstract:

    dom_simplify_tactic.h is header-only (mk_dom_simplify_tactic is defined inline); this
    translation unit exists solely so its Z3_ADD_TACTIC registration (see tactic/tactic.h)
    actually gets linked into the program -- an `inline` global's constructor only runs if
    some compiled translation unit includes the header declaring it.

--*/
#include "tactic/core/dom_simplify_tactic.h"
