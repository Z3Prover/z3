/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    special_relations_tactic.h

Abstract:

    Detect special relations in an axiomatization, 
    rewrite goal using special relations.

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-28

Notes:

--*/
#pragma once

#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "tactic/core/special_relations_simplifier.h"

inline tactic* mk_special_relations_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(special_relations_simplifier, m, p, s);
        });
}

/*
  ADD_TACTIC("special-relations", "detect and replace by special relations.", "mk_special_relations_tactic(m, p)")
  ADD_SIMPLIFIER("special-relations", "detect and replace by special relations.", "alloc(special_relations_simplifier, m, p, s)")
*/

