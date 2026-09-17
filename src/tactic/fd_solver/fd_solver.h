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
#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "tactic/tactic.h"

class solver;
class tactic;

solver * mk_fd_solver(ast_manager & m, params_ref const & p, bool incremental_mode = true);
tactic * mk_fd_tactic(ast_manager & m, params_ref const & p);
tactic * mk_parallel_qffd_tactic(ast_manager& m, params_ref const& p);

Z3_ADD_TACTIC(qffd, "qffd", "builtin strategy for solving QF_FD problems.", mk_fd_tactic(m, p));
Z3_ADD_TACTIC(pqffd, "pqffd", "builtin strategy for solving QF_FD problems in parallel.", mk_parallel_qffd_tactic(m, p));

