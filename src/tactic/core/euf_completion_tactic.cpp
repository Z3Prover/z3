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
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/euf_completion.h"
#include "tactic/core/euf_completion_tactic.h"

class euf_completion_tactic_factory : public dependent_expr_simplifier_factory {
public:
    dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) override {
        return alloc(euf::completion, m, s);
    }
};

tactic * mk_euf_completion_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p, alloc(euf_completion_tactic_factory), "euf-completion");
}
