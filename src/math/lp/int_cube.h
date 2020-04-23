/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_cube.h

Abstract:

    Cube finder

    This routine attempts to find a feasible integer solution
    by tightnening bounds and running an LRA solver on the 
    tighter system.

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/
#pragma once

#include "math/lp/lia_move.h"

namespace lp {
    class int_solver;
    class lar_solver;
    class int_cube {
        class int_solver& lia;
        class lar_solver& lra;
        bool tighten_term_for_cube(unsigned i);
        bool tighten_terms_for_cube();
        void find_feasible_solution();
        impq get_cube_delta_for_term(const lar_term& t) const;
    public:
        int_cube(int_solver& lia);
        ~int_cube() {}
        lia_move operator()();
    };
}
