/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    fd_solver.cpp

Abstract:

    Finite domain solver.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-17

Notes:
   
--*/

#include "fd_solver.h"
#include "tactic.h"
#include "inc_sat_solver.h"
#include "enum2bv_solver.h"
#include "pb2bv_solver.h"
#include "bounded_int2bv_solver.h"

solver * mk_fd_solver(ast_manager & m, params_ref const & p) {
    solver* s = mk_inc_sat_solver(m, p);
    s = mk_enum2bv_solver(m, p, s);
    s = mk_pb2bv_solver(m, p, s);
    s = mk_bounded_int2bv_solver(m, p, s);
    return s;
}
