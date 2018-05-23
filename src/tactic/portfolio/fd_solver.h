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

#include "ast/ast.h"
#include "util/params.h"

class solver;
class tactic;

solver * mk_fd_solver(ast_manager & m, params_ref const & p, bool incremental_mode = true);
tactic * mk_fd_tactic(ast_manager & m, params_ref const & p);
tactic * mk_parallel_qffd_tactic(ast_manager& m, params_ref const& p);

/*
    ADD_TACTIC("qffd", "builtin strategy for solving QF_FD problems.", "mk_fd_tactic(m, p)")
    ADD_TACTIC("pqffd", "builtin strategy for solving QF_FD problems in parallel.", "mk_parallel_qffd_tactic(m, p)")
*/

#endif
