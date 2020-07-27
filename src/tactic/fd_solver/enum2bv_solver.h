/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    enum2bv_solver.h

Abstract:

    Finite domain solver.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-17

Notes:
   
--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"

class solver;

solver * mk_enum2bv_solver(ast_manager & m, params_ref const & p, solver* s);

