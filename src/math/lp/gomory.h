/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/
#pragma once
#include "math/lp/lar_term.h"
#include "math/lp/lia_move.h"
#include "math/lp/explanation.h"
#include "math/lp/static_matrix.h"

namespace lp {
    class int_solver;
    class lar_solver;
    class gomory {
        class int_solver& lia;
        class lar_solver& lra;
        unsigned_vector gomory_select_int_infeasible_vars(unsigned num_cuts);
        unsigned_vector gomory_select_random_rows(unsigned num_rows);
        bool is_gomory_cut_target(lpvar j); 
        bool cut_has_enough_efficacy(const lar_term& t, const mpq& k);
        double cut_efficacy(const lar_term& t, const mpq& k);
        u_dependency* add_deps(u_dependency*, const row_strip<mpq>&, lpvar);
    public:
        lia_move get_gomory_cuts(unsigned num_cuts);
        gomory(int_solver& lia);
    };
}
