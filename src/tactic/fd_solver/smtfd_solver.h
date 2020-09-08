/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    smtfd_solver.h

Abstract:

    SMT reduction to Finite domain solver.

Author:

    Nikolaj Bjorner (nbjorner) 2019-09-03

Notes:
   
--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"

class solver;
class tactic;

solver * mk_smtfd_solver(ast_manager & m, params_ref const & p);
tactic * mk_smtfd_tactic(ast_manager & m, params_ref const & p);

/*
    ADD_TACTIC("smtfd", "builtin strategy for solving SMT problems by reduction to FD.", "mk_smtfd_tactic(m, p)")
*/

