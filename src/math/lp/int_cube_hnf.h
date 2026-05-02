/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    int_cube_hnf.h

Abstract:

    HNF-cube finder.

    Generalization of int_cube. Instead of the unit cube C = [-1/2, 1/2]^n
    we use a parallelepiped K = U * C where U is an n x n unimodular
    integer matrix obtained by column-reducing the (matrix of integer
    coefficients of currently-active term rows). For each term row a
    we use the support function

        h_K(a) = (1/2) * || U^T a ||_1 = (1/2) * || (A * U)_row ||_1

    which is the ell_1 norm of the row in the reduced matrix H = A U.
    Tighter than (1/2) ||a||_1 in general; in particular, integer
    diophantine sub-rows collapse to gcd-sized entries.

    For each integer non-term column j in J we tighten its [lb, ub]
    bound by

        delta_j = (1/2) * || (U)_row_j ||_1.

    After the tightened LP is feasible we round x_J* by

        y* = U^{-1} x_J*,
        z  = U * round(y*).

Author:
    Lev Nachmanson (levnach)

Revision History:

--*/
#pragma once

#include "math/lp/lia_move.h"
#include "math/lp/numeric_pair.h"
#include "util/vector.h"

namespace lp {
    class int_solver;
    class lar_solver;
    class lar_term;

    class int_cube_hnf {
        class int_solver&     lia;
        class lar_solver&     lra;

        vector<unsigned>            m_J;
        vector<unsigned>            m_col_to_J;
        vector<unsigned>            m_term_js;
        vector<vector<mpq>>         m_H;
        vector<vector<mpq>>         m_U;
        vector<vector<mpq>>         m_U_inv;
        vector<impq>                m_term_delta;
        vector<impq>                m_col_delta;
        vector<impq>                m_saved_x_J;

    public:
        int_cube_hnf(int_solver& lia);
        lia_move operator()();

    private:
        bool collect_J_and_terms();
        bool build_matrix();
        bool compute_hnf();
        bool too_big(const mpq& v) const;
        bool column_bounds_are_integral(unsigned j) const;
        bool tighten_terms_for_hnf_cube();
        bool tighten_columns_for_hnf_cube();
        bool tighten_column_bound_by_delta(unsigned j, const impq& delta);
        void compute_deltas();
        void save_x_J();
        void apply_rounding();
    };
}
