/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion_tactic.cpp

Abstract:

    Tactic for simplifying with equations.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/

#include "tactic/tactic.h"
#include "tactic/core/euf_completion_tactic.h"

tactic * mk_euf_completion_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(euf::completion, m, s); });
}
