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

solver * mk_simplifier_solver(solver * s);

