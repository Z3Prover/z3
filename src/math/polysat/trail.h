/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat trail

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"

namespace polysat {

    enum class trail_instr_t {
        qhead_i,
        lemma_qhead_i,
        add_lemma_i,
        // pwatch_i,
        add_var_i,
        inc_level_i,
        viable_add_i,
        viable_rem_i,
        viable_constraint_i,
        assign_i,
        assign_bool_i
    };

}
