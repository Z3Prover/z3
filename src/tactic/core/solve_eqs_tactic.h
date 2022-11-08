/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solve_eqs_tactic.h

Abstract:

    Tactic for solving equations and performing gaussian elimination.

Author:

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_solve_eqs1_tactic(ast_manager & m, params_ref const & p = params_ref());

#if 0
inline tactic * mk_solve_eqs_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return mk_solve_eqs1_tactic(m, p);
}
#endif

/*
  ADD_TACTIC("solve-eqs", "eliminate variables by solving equations.", "mk_solve_eqs1_tactic(m, p)")
*/


