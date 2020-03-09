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

#include "math/lp/lia_move.h"

namespace lp {
    class int_solver;
    class lar_solver;
    class int_branch {
        class int_solver& lia;
        class lar_solver& lra;
        lia_move create_branch_on_column(int j);
        bool left_branch_is_more_narrow_than_right(unsigned j);
        int find_inf_int_base_column();
        int get_kth_inf_int(unsigned k) const;
        int find_inf_int_nbasis_column() const;
        int find_any_inf_int_column_basis_first();
        int find_inf_int_boxed_base_column_with_smallest_range(unsigned & inf_int_count);

    public:
        int_branch(int_solver& lia);
        ~int_branch() {}
        lia_move operator()();
    };
}
