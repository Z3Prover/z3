/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    combined_solver.cpp

Abstract:

    Implements the solver API by combining two solvers.

    This is a replacement for the strategic_solver class.

Author:

    Leonardo (leonardo) 2012-12-11

Notes:

--*/
#pragma once

#include "util/params.h"

class ast_manager;
class expr;
using solver_routing_predicate = bool (*)(ast_manager &, expr *);

class solver;
class solver_factory;

solver * mk_combined_solver(solver * s1, solver * s2, params_ref const & p, solver_routing_predicate prefer_solver1 = nullptr);
solver_factory * mk_combined_solver_factory(solver_factory * f1, solver_factory * f2);


