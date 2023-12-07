/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_branch.h

Abstract:

    Branch heuristic

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/
#pragma once

#include "math/lp/lar_solver.h"
#include "math/lp/int_solver.h"
#include "math/lp/lia_move.h"

namespace lp {
    class int_solver;
    class lar_solver;
    class int_branch {
        class int_solver& lia;
        class lar_solver& lra;
        lia_move create_branch_on_column(int j);
        int find_inf_int_base_column();

    public:
        int_branch(int_solver& lia);
        lia_move operator()();
    };
}
