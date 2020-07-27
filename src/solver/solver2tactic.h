/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    solver2tactic.h

Abstract:

    Convert solver to a tactic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-17

Notes:
   
--*/
#pragma once

#include "tactic/tactic.h"
#include "tactic/generic_model_converter.h"
class solver;

tactic * mk_solver2tactic(solver* s);

void extract_clauses_and_dependencies(goal_ref const& g, expr_ref_vector& clauses, ptr_vector<expr>& assumptions, obj_map<expr, expr*>& bool2dep, ref<generic_model_converter>& fmc);

