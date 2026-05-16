/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    int_cube_lll.h

Abstract:

    LLL-style cube heuristic for the integer-LP solver.

    Generalization of int_cube. Instead of the unit cube C = [-1/2, 1/2]^n
    we use a parallelepiped K = B * C, where B is an n x n unimodular
    integer matrix found by a *monotone* greedy basis-reduction that
    minimizes the actual cube cost

        C(B) = (1/2) * (||A * B||_1 + ||B||_1)
             = sum_r delta_row(r, B) + sum_j delta_col(j, B)

    over GL_n(Z). Atomic move is a single elementary column operation

        col_j(B) <- col_j(B) - q * col_k(B)    (q in Z, j != k)

    The q candidates for a fixed pair (j, k) include the floor/ceil of the
    weighted median of the breakpoints {A_row(r,j)/A_row(r,k)} and
    {B(i,j)/B(i,k)} (weights are the absolute values of the denominators).
    They are scored lexicographically: first minimize the number/severity
    of bounded rows/columns whose later delta-tightening would collapse
    their box, then minimize C(B). This keeps the greedy from accepting a
    cost-improving basis move that merely sets up a bail-tighten failure.
    Soundness: after the basis search completes we compare the unweighted
    C(B) against the identity baseline C(I) = ||A||_1 + n; if the basis
    failed to strictly improve it we bail back to plain int_cube semantics.
    The heuristic is therefore never worse than the plain int_cube.

    This addresses the regression of int_cube_hnf, whose triangulation
    can blow up the column-delta term ||B||_1: in 153 random instances
    (3x3 to 5x5, coefficients in [-20, 20]) HNF cube lost to plain cube
    on >99% of inputs, with an average cost ratio of 3x-50x worse, while
    pairwise-greedy LLL won or tied on 100% (see findings.md in the
    session-state).

    Soundness: identical to int_cube_hnf. We work with a saved column
    snapshot of x_J, tighten the LP, find a real-feasible point x*, and
    round y* = B^{-1} x* to nearest integer in lattice coordinates, then
    lift z = B * round(y*).

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

    class int_cube_lll {
        class int_solver&     lia;
        class lar_solver&     lra;

        // Per-row/column metadata cached for the duration of one operator()
        // call.  All fields are invariants of the LP bounds and lattice
        // structure (lra is read-only during compute_basis), so they are
        // computed once in init_pair_invariants() instead of being rebuilt
        // inside every reduce_pair(j, k) call.
        struct row_meta {
            bool eligible;       // column_has_lower_bound && column_has_upper_bound
            mpq  width;          // ub - lb (when eligible)
            bool integral_unit;  // column_bounds_are_integral(var)
        };

        vector<unsigned>            m_J;
        vector<unsigned>            m_col_to_J;
        vector<unsigned>            m_term_js;
        vector<vector<mpq>>         m_H;       // H = A * B; m x n
        vector<vector<mpq>>         m_B;       // n x n unimodular
        vector<vector<mpq>>         m_B_inv;   // B^{-1} = product of inverse elementaries
        vector<mpq>                 m_col_w;   // per-column weight in the cube cost
        vector<row_meta>            m_term_meta;   // per term row of H
        vector<row_meta>            m_col_meta;    // per J column (row of B)
        vector<mpq>                 m_row_sum_H;   // ||row_r(H)||_1, maintained incrementally
        vector<mpq>                 m_row_sum_B;   // ||row_i(B)||_1, maintained incrementally
        mpq                         m_baseline_cost; // unweighted C(B) at B = I
        mpq                         m_total_cost;    // current unweighted C(B)
        vector<impq>                m_term_delta;
        vector<impq>                m_col_delta;
        vector<impq>                m_saved_x_J;

    public:
        int_cube_lll(int_solver& lia);
        lia_move operator()();

    private:
        bool collect_J_and_terms();
        bool build_matrix();
        void compute_col_weights();
        void init_pair_invariants();
        bool compute_basis();
        bool reduce_pair(unsigned j, unsigned k, bool& improved);
        bool too_big(const mpq& v) const;
        bool column_bounds_are_integral(unsigned j) const;
        bool tighten_terms_for_lll_cube();
        bool tighten_columns_for_lll_cube();
        bool tighten_column_bound_by_delta(unsigned j, const impq& delta);
        void compute_deltas();
        void save_x_J();
        void apply_rounding();
    };
}
