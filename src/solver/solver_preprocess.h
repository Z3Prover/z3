/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solver_preprocess.h

Abstract:

    SAT pre-process initialization
    It collects the functionality associated with 
    initializing pre-processing for the sat-smt solver.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-28

--*/

#pragma once

#include "ast/simplifiers/then_simplifier.h"

void init_preprocess(ast_manager& m, params_ref const& p, then_simplifier& s, dependent_expr_state& st);

