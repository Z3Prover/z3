/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    split_clause_tactic.h

Abstract:

    Tactic that creates a subgoal for each literal in a clause (l_1 or ... or l_n).
    The tactic fails if the main goal does not contain any clause.

Author:

    Leonardo (leonardo) 2011-11-21

Notes:

--*/
#pragma once

#include "util/params.h"
class tactic;

tactic * mk_split_clause_tactic(params_ref const & p = params_ref());

/*
  ADD_TACTIC("split-clause", "split a clause in many subgoals.", "mk_split_clause_tactic(p)")
*/

