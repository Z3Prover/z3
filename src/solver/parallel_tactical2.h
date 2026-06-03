/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parallel_tactical2.h

Abstract:

    Parallel portfolio solver using the solver API.
    Models the internals after smt/smt_parallel.cpp but operates
    on generic solver objects instead of smt::context.

Author:

    (based on smt_parallel.cpp and parallel_tactical.cpp)

--*/
#pragma once

class tactic;
class solver;
class params_ref;

tactic * mk_parallel_tactic2(solver* s, params_ref const& p);
