/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    pb2bv_solver.h

Abstract:

    Pseudo-Boolean to bit-vector solver.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:
   
--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"

class solver;

solver * mk_pb2bv_solver(ast_manager & m, params_ref const & p, solver* s);

