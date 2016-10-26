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
#ifndef SOLVER2TACTIC_H_
#define SOLVER2TACTIC_H_

#include "tactic.h"
#include "filter_model_converter.h"
class solver;

tactic * mk_solver2tactic(solver* s);

void extract_clauses_and_dependencies(goal_ref const& g, expr_ref_vector& clauses, ptr_vector<expr>& assumptions, obj_map<expr, expr*>& bool2dep, ref<filter_model_converter>& fmc);

#endif
