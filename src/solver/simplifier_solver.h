/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    simplifier_solver.cpp

Abstract:

    Implements a solver with simplifying pre-processing.

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-30

--*/
#pragma once

#include "util/params.h"

class solver;
class solver_factory;
class dependent_expr_simplifier;
class dependent_expr_state;
typedef std::function<dependent_expr_simplifier*(ast_manager&, const params_ref&, dependent_expr_state& s)> simplifier_factory;

solver * mk_simplifier_solver(solver * s, simplifier_factory* fac);

