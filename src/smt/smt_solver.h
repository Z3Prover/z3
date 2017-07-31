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
#ifndef SMT_SOLVER_H_
#define SMT_SOLVER_H_

#include "ast/ast.h"
#include "util/params.h"

class solver;
class solver_factory;

solver * mk_smt_solver(ast_manager & m, params_ref const & p, symbol const & logic);
solver_factory * mk_smt_solver_factory();

#endif
