/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    purify_arith_tactic.h

Abstract:

    Tactic for eliminating arithmetic operators: DIV, IDIV, MOD,
    TO_INT, and optionally (OP_IRRATIONAL_ALGEBRAIC_NUM).

    This tactic uses the simplifier for also eliminating:
    OP_SUB, OP_UMINUS, OP_POWER (optionally), OP_REM, OP_IS_INT. 
    
Author:

    Leonardo de Moura (leonardo) 2011-12-30.

Revision History:

--*/
#include "tactic/tactical.h"
#include "tactic/arith/purify_arith_tactic.h"

tactic * mk_purify_arith_tactic(ast_manager & m, params_ref const & p) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(purify_arith_simplifier, m, p, s);
        });
}
