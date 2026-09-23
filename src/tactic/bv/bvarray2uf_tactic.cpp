/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bvarray2uf_tactic.cpp

Abstract:

    bvarray2uf_tactic.h is header-only (mk_bvarray2uf_tactic is defined inline); this
    translation unit exists solely so its Z3_ADD_TACTIC registration (see tactic/tactic.h)
    actually gets linked into the program -- an `inline` global's constructor only runs if
    some compiled translation unit includes the header declaring it.

--*/
#include "tactic/bv/bvarray2uf_tactic.h"
