/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    parallel_tactical.cpp

Abstract:

    Compatibility entry point for the parallel tactic.

    The original implementation in this file duplicated parts of
    smt/smt_parallel.cpp but could not faithfully mirror the SMT behavior
    because it only had access to the generic solver API, not smt::context.
    The solver-agnostic implementation now lives in parallel_tactical2.cpp
    and models the smt_parallel search-tree/worker design using only the
    solver interface so it also works for SAT and other solver subclasses.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-9
    Miguel Neves

--*/

#include "solver/parallel_tactical.h"
#include "solver/parallel_tactical2.h"

tactic* mk_parallel_tactic(solver* s, params_ref const& p) {
    return mk_parallel_tactic2(s, p);
}
