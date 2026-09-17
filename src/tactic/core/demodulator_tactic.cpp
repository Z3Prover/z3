/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    demodulator_tactic.cpp

Abstract:

    demodulator_tactic.h is header-only (mk_demodulator_tactic is defined inline); this
    translation unit exists solely so its Z3_ADD_TACTIC registration (see tactic/tactic.h)
    actually gets linked into the program -- an `inline` global's constructor only runs if
    some compiled translation unit includes the header declaring it.

--*/
#include "tactic/core/demodulator_tactic.h"
