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

#include "tactic/fd_solver/fd_solver.h"
#include "tactic/tactic.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "tactic/fd_solver/enum2bv_solver.h"
#include "tactic/fd_solver/pb2bv_solver.h"
#include "tactic/fd_solver/bounded_int2bv_solver.h"
#include "solver/solver2tactic.h"
#include "solver/parallel_tactic.h"
#include "solver/parallel_params.hpp"

solver * mk_fd_solver(ast_manager & m, params_ref const & p, bool incremental_mode) {
    solver* s = mk_inc_sat_solver(m, p, incremental_mode);
    s = mk_enum2bv_solver(m, p, s);
    s = mk_pb2bv_solver(m, p, s);
    s = mk_bounded_int2bv_solver(m, p, s);
    return s;
}

static tactic * mk_seq_fd_tactic(ast_manager & m, params_ref const& p) {
    return mk_solver2tactic(mk_fd_solver(m, p, false));
}

tactic * mk_parallel_qffd_tactic(ast_manager& m, params_ref const& p) {
    return mk_parallel_tactic(mk_fd_solver(m, p), p);
}


tactic * mk_fd_tactic(ast_manager & m, params_ref const& _p) {
    parallel_params pp(_p);
    params_ref p = _p;
    return pp.enable() ? mk_parallel_qffd_tactic(m, p) : mk_seq_fd_tactic(m, p);
}

