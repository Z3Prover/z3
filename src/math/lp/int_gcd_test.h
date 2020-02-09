/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_gcd_test.h

Abstract:

    Gcd_Test heuristic

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
    class int_gcd_test {
        class int_solver& lia;
        class lar_solver& lra;

        bool gcd_test();
        bool gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i);
        bool ext_gcd_test(const row_strip<mpq> & row,
                                        mpq const & least_coeff, 
                                        mpq const & lcm_den,
                                        mpq const & consts);
        void fill_explanation_from_fixed_columns(const row_strip<mpq> & row);

    public:
        int_gcd_test(int_solver& lia);
        ~int_gcd_test() {}
        lia_move operator()();
    };
}
