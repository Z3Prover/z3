/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    horn_tactic.h

Abstract:

    PDR as a tactic to solve Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-16.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_horn_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("horn", "apply tactic for horn clauses.", "mk_horn_tactic(m, p)")
*/

tactic * mk_horn_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("horn-simplify", "simplify horn clauses.", "mk_horn_simplify_tactic(m, p)")
*/
