/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_pareto_solver.h

Abstract:

    Incremental nlsat backend for polynomial real Pareto problems.

--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"

class solver;

namespace opt {
    bool can_reuse_nlsat_solver(expr_ref_vector const& terms);
    solver* mk_pareto_nlsat_solver(ast_manager& m, params_ref const& p);
}
