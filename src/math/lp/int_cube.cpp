/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    int_cube.cpp

Abstract:

    Cube finder

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

Revision History:
--*/

#include <algorithm>
#include <unordered_map>

#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/int_cube.h"

namespace lp {

    int_cube::int_cube(int_solver& lia):lia(lia), lra(lia.lra) {}

    lia_move int_cube::operator()() {
        lia.settings().stats().m_cube_calls++;
        TRACE(cube,
              for (unsigned j = 0; j < lra.number_of_vars(); ++j)
                  lia.display_column(tout, j);
              tout << lra.constraints();
              );
        
        lra.push();
        if (!tighten_terms_for_cube()) {
            lra.pop();
            lra.set_status(lp_status::OPTIMAL);
            return lia_move::undef;
        }
        
        lp_status st = lra.find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            TRACE(cube, tout << "cannot find a feasible solution";);
            lra.pop();
            lra.move_non_basic_columns_to_bounds();
            // it can happen that we found an integer solution here
            return !lra.r_basis_has_inf_int()? lia_move::sat: lia_move::undef;
        }
        lra.pop();
        lra.round_to_integer_solution();
        lra.set_status(lp_status::FEASIBLE);
        SASSERT(lia.settings().get_cancel_flag() || lia.is_feasible());
        TRACE(cube, tout << "success";);
        lia.settings().stats().m_cube_success++;
        return lia_move::sat;
    }
// i is the column index having the term
    bool int_cube::tighten_term_for_cube(unsigned i) {
        if (!lra.column_associated_with_row(i))
            return true;
        const lar_term& t = lra.get_term(i);
        impq delta = get_cube_delta_for_term(t);
        TRACE(cube, lra.print_term_as_indices(t, tout); tout << ", delta = " << delta << "\n";);
        if (is_zero(delta))
            return true;
        return lra.tighten_term_bounds_by_delta(i, delta);
    }
    
    bool int_cube::tighten_terms_for_cube() {
        for (const lar_term* t: lra.terms())
            if (!tighten_term_for_cube(t->j())) {
                TRACE(cube, tout << "cannot tighten";);
                return false;
            }
        return true;
    }

    void int_cube::find_feasible_solution() {
        lra.find_feasible_solution();
        SASSERT(lp_status::OPTIMAL == lra.get_status() || lp_status::FEASIBLE == lra.get_status());
    }

    // The largest cube test of Bromberger and Weidenbach:
    //     maximize x_e subject to Ax + a'(x_e/2) <= b, x_e >= 0, where a'_i = ||a_i||_1,
    // with the 1-norm taken over the integer variables of the row.
    // The solution is the center z of a largest cube contained in the polyhedron.
    // If the maximal edge length is at least 1, then the rounding of z is
    // an integer solution; otherwise the rounding is checked, and possibly repaired,
    // against the original constraints.
    lia_move int_cube::find_largest_cube() {
        lia.settings().stats().m_lcube_calls++;
        TRACE(cube,
              for (unsigned j = 0; j < lra.number_of_vars(); ++j)
                  lia.display_column(tout, j);
              tout << lra.constraints();
              );

        lra.push();
        // The edge rows are ephemeral: suppress the add-term callback,
        // dioph_eq's reaction to it is not undone by pop().
        auto add_term_cb = lra.m_add_term_callback;
        lra.m_add_term_callback = nullptr;
        unsigned x_e = lra.add_var(UINT_MAX, false); // the edge length of the cube
        lra.add_var_bound(x_e, lconstraint_kind::GE, mpq(0));
        bool ok = add_cube_edge_rows(x_e);
        lra.m_add_term_callback = add_term_cb;
        if (!ok) {
            lra.pop();
            lra.set_status(lp_status::OPTIMAL);
            return lia_move::undef;
        }

        lp_status st = lra.find_feasible_solution();
        if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
            TRACE(cube, tout << "cannot find a feasible solution";);
            lra.pop();
            lra.move_non_basic_columns_to_bounds();
            // it can happen that we found an integer solution here
            return !lra.r_basis_has_inf_int()? lia_move::sat: lia_move::undef;
        }

        impq e; // the maximal edge length
        st = lra.maximize_term(x_e, e, /*fix_int_cols*/ false);
        if (lia.settings().get_cancel_flag()) {
            lra.pop();
            return lia_move::undef;
        }
        if (st == lp_status::UNBOUNDED) {
            // infinite lattice width: the polyhedron contains cubes of arbitrary edge length
            lra.add_var_bound(x_e, lconstraint_kind::GE, mpq(1));
            st = lra.find_feasible_solution();
            if (st != lp_status::FEASIBLE && st != lp_status::OPTIMAL) {
                lra.pop();
                return lia_move::undef;
            }
            lra.pop();
            return sat_after_rounding();
        }
        TRACE(cube, tout << "max edge length = " << e << "\n";);
        if (e >= impq(mpq(1))) {
            lra.pop();
            return sat_after_rounding();
        }
        // the largest cube is smaller than the unit cube:
        // the rounded center is only a candidate
        lra.pop();
        return round_and_repair();
    }

    bool int_cube::add_cube_edge_rows(unsigned x_e) {
        // snapshot the term columns: add_edge_rows_for_term appends to lra.terms()
        svector<unsigned> term_columns;
        for (const lar_term* t : lra.terms())
            term_columns.push_back(t->j());
        for (unsigned j : term_columns)
            if (!add_edge_rows_for_term(j, x_e)) {
                TRACE(cube, tout << "cannot add the edge rows";);
                return false;
            }
        return true;
    }

    // i is the column index having the term
    bool int_cube::add_edge_rows_for_term(unsigned i, unsigned x_e) {
        if (!lra.column_associated_with_row(i))
            return true;
        const lar_term& t = lra.get_term(i);
        impq delta = get_cube_delta_for_term(t);
        TRACE(cube, lra.print_term_as_indices(t, tout); tout << ", delta = " << delta << "\n";);
        if (is_zero(delta))
            return true;
        if (!is_zero(delta.y))
            // the infinitesimal delta does not scale with x_e: tighten statically,
            // it is sound for any edge length
            return lra.tighten_term_bounds_by_delta(i, delta);
        if (lra.column_has_upper_bound(i)) {
            impq u = lra.get_upper_bound(i); // copy: add_term invalidates bound references
            vector<std::pair<mpq, unsigned>> coeffs;
            coeffs.push_back(std::make_pair(mpq(1), i));
            coeffs.push_back(std::make_pair(delta.x, x_e));
            unsigned s = lra.add_term(coeffs, UINT_MAX);
            lra.add_var_bound(s, is_zero(u.y) ? lconstraint_kind::LE : lconstraint_kind::LT, u.x);
        }
        if (lra.column_has_lower_bound(i)) {
            impq l = lra.get_lower_bound(i); // copy: add_term invalidates bound references
            vector<std::pair<mpq, unsigned>> coeffs;
            coeffs.push_back(std::make_pair(mpq(1), i));
            coeffs.push_back(std::make_pair(-delta.x, x_e));
            unsigned s = lra.add_term(coeffs, UINT_MAX);
            lra.add_var_bound(s, is_zero(l.y) ? lconstraint_kind::GE : lconstraint_kind::GT, l.x);
        }
        return true;
    }

    lia_move int_cube::sat_after_rounding() {
        lra.round_to_integer_solution();
        lra.set_status(lp_status::FEASIBLE);
        SASSERT(lia.settings().get_cancel_flag() || lia.is_feasible());
        TRACE(cube, tout << "largest cube success";);
        lia.settings().stats().m_lcube_success++;
        return lia_move::sat;
    }

    lia_move int_cube::round_and_repair() {
        lra.backup_x(); // remember the cube center
        vector<flip_candidate> flips;
        for (unsigned j = 0; j < lra.column_count(); ++j) {
            if (!lra.column_is_int(j) || lra.column_has_term(j))
                continue;
            const impq& v = lra.get_column_value(j);
            if (v.is_int())
                continue;
            flip_candidate f;
            f.m_j = j;
            f.m_lo = floor(v);
            flips.push_back(f);
        }
        lra.round_to_integer_solution();
        for (auto& f : flips)
            f.m_at_hi = lra.get_column_value(f.m_j).x > f.m_lo;
        if (repair_rounded_candidate(flips)) {
            lra.set_status(lp_status::FEASIBLE);
            SASSERT(lia.settings().get_cancel_flag() || lia.is_feasible());
            TRACE(cube, tout << "largest cube success";);
            lia.settings().stats().m_lcube_success++;
            return lia_move::sat;
        }
        // return to the cube center: an interior point of the polyhedron
        lra.restore_x();
        lra.set_status(lp_status::FEASIBLE);
        return lia_move::undef;
    }

    // Checks the rounded center against the original constraints. On failure
    // searches the vertices of the lattice cell around the center greedily:
    // flip a coordinate between floor and ceiling to maximally decrease the
    // total bound violation, within a budget.
    bool int_cube::repair_rounded_candidate(vector<flip_candidate>& flips) {
        vector<bounded_row> rows;
        for (const lar_term* t : lra.terms()) {
            unsigned j = t->j();
            if (!lra.column_associated_with_row(j))
                continue;
            if (!lra.column_has_upper_bound(j) && !lra.column_has_lower_bound(j))
                continue;
            bounded_row r;
            r.m_j = j;
            r.m_val = t->apply(lra.r_x());
            rows.push_back(r);
        }
        auto row_violation = [&](unsigned ri, const impq& v) {
            impq w;
            unsigned j = rows[ri].m_j;
            if (lra.column_has_upper_bound(j) && v > lra.get_upper_bound(j))
                w += v - lra.get_upper_bound(j);
            if (lra.column_has_lower_bound(j) && v < lra.get_lower_bound(j))
                w += lra.get_lower_bound(j) - v;
            return w;
        };
        impq violation;
        for (unsigned ri = 0; ri < rows.size(); ++ri)
            violation += row_violation(ri, rows[ri].m_val);
        if (is_zero(violation))
            return true; // the rounded center fits as it is
        if (flips.empty())
            return false;

        std::unordered_map<unsigned, unsigned> flip_of_var;
        for (unsigned fi = 0; fi < flips.size(); ++fi)
            flip_of_var[flips[fi].m_j] = fi;
        // occurrences of the flip candidates in the bounded rows
        vector<vector<std::pair<unsigned, mpq>>> occs;
        occs.resize(flips.size());
        for (unsigned ri = 0; ri < rows.size(); ++ri) {
            const lar_term& t = lra.get_term(rows[ri].m_j);
            for (lar_term::ival p : t) {
                auto it = flip_of_var.find(p.j());
                if (it != flip_of_var.end())
                    occs[it->second].push_back(std::make_pair(ri, p.coeff()));
            }
        }

        unsigned budget = std::min(2 * flips.size(), lia.settings().lcube_flips());
        bool flipped = false;
        while (!is_zero(violation) && budget-- > 0) {
            unsigned best_fi = UINT_MAX;
            impq best_gain;
            for (unsigned fi = 0; fi < flips.size(); ++fi) {
                if (occs[fi].empty())
                    continue;
                mpq step = flips[fi].m_at_hi ? mpq(-1) : mpq(1);
                impq gain;
                for (const auto& o : occs[fi]) {
                    const impq& v = rows[o.first].m_val;
                    gain += row_violation(o.first, v + impq(step * o.second)) - row_violation(o.first, v);
                }
                if (gain < best_gain) {
                    best_gain = gain;
                    best_fi = fi;
                }
            }
            if (best_fi == UINT_MAX)
                return false; // no flip decreases the violation
            mpq step = flips[best_fi].m_at_hi ? mpq(-1) : mpq(1);
            for (const auto& o : occs[best_fi])
                rows[o.first].m_val += impq(step * o.second);
            flips[best_fi].m_at_hi = !flips[best_fi].m_at_hi;
            violation += best_gain;
            flipped = true;
            TRACE(cube, tout << "flipped column " << flips[best_fi].m_j << ", violation = " << violation << "\n";);
        }
        if (!is_zero(violation))
            return false;

        // apply the repaired candidate
        for (const auto& f : flips)
            lra.set_column_value(f.m_j, impq(f.m_at_hi ? f.m_lo + 1 : f.m_lo));
        for (const lar_term* t : lra.terms()) {
            unsigned j = t->j();
            if (!lra.column_associated_with_row(j))
                continue;
            lra.set_column_value(j, t->apply(lra.r_x()));
        }
        if (flipped)
            lia.settings().stats().m_lcube_flip_success++;
        return true;
    }

    impq int_cube::get_cube_delta_for_term(const lar_term& t) const {
        if (t.size() == 2) {
            bool seen_minus = false;
            bool seen_plus = false;
            for(lar_term::ival p : t) {
                if (!lia.column_is_int(p.j()))
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
        for (lar_term::ival p : t)
            if (lia.column_is_int(p.j()))
                delta += abs(p.coeff());
        
        delta *= mpq(1, 2);
        return impq(delta);
    }

}
