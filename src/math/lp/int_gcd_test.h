/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_gcd_test.h

Abstract:

    Gcd_Test heuristic

    gcd test
    5*x + 3*y + 6*z = 5
    suppose x is fixed at 2.
    so we have 10 + 3(y + 2z) = 5
                 5 = -3(y + 2z)
    this is unsolvable because 5/3 is not an integer.
    so we create a lemma that rules out this condition.
    

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

        struct row_parity {
            mpq m_parity;
            mpq m_modulo;
            const row_strip<mpq>* m_row = nullptr;
            row_parity(mpq const& p, mpq const& m, row_strip<mpq> const& r):
                m_parity(p),
                m_modulo(m),
                m_row(&r)
            {}
        };
        class int_solver& lia;
        class lar_solver& lra;
        unsigned m_next_gcd;
        unsigned m_delay;
        mpq m_consts;
        mpq m_least_coeff;
        mpq m_lcm_den;
        unsigned_vector            m_inserted_rows;
        vector<vector<row_parity>> m_row_parities;

        void reset_parities();
        bool insert_row_parity(unsigned j, row_strip<mpq> const& r, mpq const& parity, mpq const& modulo);

        bool gcd_test();
        bool gcd_test_for_row(const static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i);
        bool ext_gcd_test(const row_strip<mpq> & row);
        void fill_explanation_from_fixed_columns(const row_strip<mpq> & row);
        void add_to_explanation_from_fixed_or_boxed_column(unsigned j);
        bool accumulate_parity(const row_strip<mpq> & row, unsigned least_coeff_index);
    public:
        int_gcd_test(int_solver& lia);
        lia_move operator()();
        bool should_apply();
    };
}
