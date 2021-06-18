/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    cmd_context_to_goal.cpp

Abstract:
    Procedure for copying the assertions in the
    command context to a goal object.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:

--*/
#include "cmd_context/cmd_context.h"
#include "tactic/goal.h"

/**
   \brief Assert expressions from ctx into t.
*/
void assert_exprs_from(cmd_context const & ctx, goal & t) {
    if (ctx.produce_proofs() && ctx.produce_unsat_cores()) 
        throw cmd_exception("Frontend does not support simultaneous generation of proofs and unsat cores");
    if (ctx.produce_unsat_cores() && ctx.assertions().size() != ctx.assertion_names().size())
        throw cmd_exception("Unsat core tracking must be set before assertions are added");
    ast_manager & m = t.m();
    bool proofs_enabled = t.proofs_enabled();
    if (ctx.produce_unsat_cores()) {
        ptr_vector<expr>::const_iterator it   = ctx.assertions().begin();
        ptr_vector<expr>::const_iterator end  = ctx.assertions().end();
        ptr_vector<expr>::const_iterator it2  = ctx.assertion_names().begin();
        for (; it != end; ++it, ++it2) {
            t.assert_expr(*it, proofs_enabled ? m.mk_asserted(*it) : nullptr, m.mk_leaf(*it2));
        }
    }
    else {
        for (expr * e : ctx.assertions()) {
            t.assert_expr(e, proofs_enabled ? m.mk_asserted(e) : nullptr, nullptr);
        }
        SASSERT(ctx.assertion_names().empty());
    }
}
