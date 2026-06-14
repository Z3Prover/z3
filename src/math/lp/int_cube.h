/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_cube.h

Abstract:

    Cube finder

    This routine attempts to find a feasible integer solution
    by tightnening bounds and running an LRA solver on the
    tighter system.

    find_largest_cube() implements the largest cube test of
    Bromberger and Weidenbach (Fast Cube Tests for LIA Constraint
    Solving, IJCAR 2016): a fresh variable x_e for the cube edge
    length is introduced and maximized; the center of the largest
    cube is rounded to a candidate integer solution.

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/
#pragma once

#include "util/vector.h"
#include "math/lp/lia_move.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/lar_term.h"

namespace lp {
    class int_solver;
    class lar_solver;
    class int_cube {
        class int_solver& lia;
        class lar_solver& lra;
        // a fractional integer coordinate of the cube center:
        // the candidate value is m_lo or m_lo + 1
        struct flip_candidate {
            unsigned m_j = 0;
            mpq      m_lo;
            bool     m_at_hi = false;
        };
        // a term column with at least one bound, tracked during the repair
        struct bounded_row {
            unsigned m_j = 0;
            impq     m_val;
        };
        bool tighten_term_for_cube(unsigned i);
        bool tighten_terms_for_cube();
        void find_feasible_solution();
        impq get_cube_delta_for_term(const lar_term& t) const;
        bool add_edge_rows_for_term(unsigned i, unsigned x_e);
        bool add_cube_edge_rows(unsigned x_e);
        lia_move sat_after_rounding();
        lia_move round_and_repair();
        bool repair_rounded_candidate(vector<flip_candidate>& flips);
    public:
        int_cube(int_solver& lia);
        lia_move operator()();
        lia_move find_largest_cube();
    };
}
