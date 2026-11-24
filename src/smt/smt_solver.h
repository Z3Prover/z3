/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.h

Abstract:

    Wraps smt::kernel as a solver for the external API and cmd_context.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:
   
    This file was called default_solver.h. It was a bad name.

--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"

class solver;
class solver_factory;

// Relax array completeness only for internal solvers whose clients validate candidates.
solver * mk_smt_solver(ast_manager & m, params_ref const & p, symbol const & logic, bool array_fake_support = false);
// Read an internal SMT solver's theory value without executing model definitions.
bool smt_solver_get_value(solver* s, expr* e, expr_ref& value);
solver_factory * mk_smt_solver_factory();

