/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_cube.cpp

Abstract:

    Cube finder

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:
--*/

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_cube.h"

namespace lp {

    int_cube::int_cube(int_solver& lia):lia(lia), lra(lia.lra) {}

    lia_move int_cube::operator()() {
        lia.settings().stats().m_cube_calls++;
        TRACE("cube",
              for (unsigned j = 0; j < lra.A_r().column_count(); j++)
                  lia.display_column(tout, j);
              tout << lra.constraints();
              );
        
        lra.push();
        if (!tighten_terms_for_cube()) {
            lra.pop();
            return lia_move::undef;
        }
        
        lp_status st = lra.find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            TRACE("cube", tout << "cannot find a feasiblie solution";);
            lra.pop();
            lra.move_non_basic_columns_to_bounds();
            find_feasible_solution();
            // it can happen that we found an integer solution here
            return !lra.r_basis_has_inf_int()? lia_move::sat: lia_move::undef;
        }
        lra.pop();
        lra.round_to_integer_solution();
        lra.set_status(lp_status::FEASIBLE);
        lp_assert(lia.settings().get_cancel_flag() || lia.is_feasible());
        TRACE("cube", tout << "success";);
        lia.settings().stats().m_cube_success++;
        return lia_move::sat;
    }

    bool int_cube::tighten_term_for_cube(unsigned i) {
        unsigned ti = i + lra.terms_start_index();
        if (!lra.term_is_used_as_row(ti))
            return true;
        const lar_term* t = lra.terms()[i];
        impq delta = get_cube_delta_for_term(*t);
        TRACE("cube", lra.print_term_as_indices(*t, tout); tout << ", delta = " << delta;);
        if (is_zero(delta))
            return true;
        return lra.tighten_term_bounds_by_delta(i, delta);
    }
    
    bool int_cube::tighten_terms_for_cube() {
        for (unsigned i = 0; i < lra.terms().size(); i++)
            if (!tighten_term_for_cube(i)) {
                TRACE("cube", tout << "cannot tighten";);
                return false;
            }
        return true;
    }

    void int_cube::find_feasible_solution() {
        lra.find_feasible_solution();
        lp_assert(lp_status::OPTIMAL == lra.get_status() || lp_status::FEASIBLE == lra.get_status());
    }

    impq int_cube::get_cube_delta_for_term(const lar_term& t) const {
        if (t.size() == 2) {
            bool seen_minus = false;
            bool seen_plus = false;
            for(const auto & p : t) {
                if (!lia.column_is_int(p.var()))
                    goto usual_delta;
                const mpq & c = p.coeff();
                if (c == one_of_type<mpq>()) {
                    seen_plus = true;
                } else if (c == -one_of_type<mpq>()) {
                    seen_minus = true;
                } else {
                    goto usual_delta;
                }
            }
            if (seen_minus && seen_plus)
                return zero_of_type<impq>();
            return impq(0, 1);
        }
    usual_delta:
        mpq delta = zero_of_type<mpq>();
        for (const auto & p : t)
            if (lia.column_is_int(p.var()))
                delta += abs(p.coeff());
        
        delta *= mpq(1, 2);
        return impq(delta);
    }

}
