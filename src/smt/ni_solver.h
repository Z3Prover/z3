/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ni_solver.h

Abstract:
    Wrappers for smt::context that are non-incremental & (quasi-incremental).

Author:

    Leonardo (leonardo) 2011-03-30

Notes:

--*/
#ifndef _NI_SOLVER_H_
#define _NI_SOLVER_H_

#include"solver.h"
class cmd_context;

// Creates a solver that restarts from scratch for every call to check_sat
solver * mk_non_incremental_smt_solver(cmd_context & ctx);

// Creates a solver that restarts from scratch for the first call to check_sat, and then moves to incremental behavior.
solver * mk_quasi_incremental_smt_solver(cmd_context & ctx);

#endif
