/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bounded_int2bv_solver.h

Abstract:

    Finite domain solver.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:
   
--*/
#ifndef BOUNDED_INT2BV_SOLVER_H_
#define BOUNDED_INT2BV_SOLVER_H_

#include "ast/ast.h"
#include "util/params.h"

class solver;

solver * mk_bounded_int2bv_solver(ast_manager & m, params_ref const & p, solver* s);

#endif
