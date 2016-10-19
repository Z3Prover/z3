/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    fd_solver.h

Abstract:

    Finite domain solver.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-17

Notes:
   
--*/
#ifndef FD_SOLVER_H_
#define FD_SOLVER_H_

#include"ast.h"
#include"params.h"

class solver;

solver * mk_fd_solver(ast_manager & m, params_ref const & p);

#endif
