/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#include <string>
#include "util/vector.h"
#include "util/lp/lar_core_solver.h"
#include "util/lp/lar_solution_signature.h"
namespace lp {
lar_core_solver::lar_core_solver(
                                 lp_settings & settings,
                                 const column_namer & column_names
                                 ):
    m_infeasible_sum_sign(0),
    m_r_solver(m_r_A,
                    m_right_sides_dummy,
                    m_r_x,
                    m_r_basis,
                    m_r_nbasis,
                    m_r_heading,
                    m_costs_dummy,
                    m_column_types(),
                    m_r_low_bounds(),
                    m_r_upper_bounds(),
                    settings,
               column_names),
    m_d_solver(m_d_A,
                    m_d_right_sides_dummy,
                    m_d_x,
                    m_d_basis,
                    m_d_nbasis,
                    m_d_heading,
                    m_d_costs_dummy,
                    m_column_types(),
                    m_d_low_bounds,
                    m_d_upper_bounds,
                    settings,
                    column_names){}

void lar_core_solver::init_costs(bool first_time) {
    SASSERT(false); // should not be called
    // SASSERT(this->m_x.size() >= this->m_n());
    // SASSERT(this->m_column_types.size() >= this->m_n());
    // if (first_time)
    //     this->m_costs.resize(this->m_n());
    // X inf = this->m_infeasibility;
    // this->m_infeasibility = zero_of_type<X>();
    // for (unsigned j = this->m_n(); j--;)
    //     init_cost_for_column(j);
    // if (!(first_time || inf >= this->m_infeasibility)) {
    //     LP_OUT(this->m_settings, "iter = " << this->total_iterations() << std::endl);
    //     LP_OUT(this->m_settings, "inf was " << T_to_string(inf) << " and now " << T_to_string(this->m_infeasibility) << std::endl);
    //     SASSERT(false);
    // }
    // if (inf == this->m_infeasibility)
    //     this->m_iters_with_no_cost_growing++;
}


void lar_core_solver::init_cost_for_column(unsigned j) {
    /*
    // If j is a breakpoint column, then we set the cost zero.
    // When anylyzing an entering column candidate we update the cost of the breakpoints columns to get the left or the right derivative if the infeasibility function
    const numeric_pair<mpq> & x = this->m_x[j];
    // set zero cost for each non-basis column
    if (this->m_basis_heading[j] < 0) {
        this->m_costs[j] = numeric_traits<T>::zero();
        return;
    }
    // j is a basis column
    switch (this->m_column_types[j]) {
    case fixed:
    case column_type::boxed:
        if (x > this->m_upper_bounds[j]) {
            this->m_costs[j] = 1;
            this->m_infeasibility += x - this->m_upper_bounds[j];
        } else if (x < this->m_low_bounds[j]) {
            this->m_infeasibility += this->m_low_bounds[j] - x;
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case low_bound:
        if (x < this->m_low_bounds[j]) {
            this->m_costs[j] = -1;
            this->m_infeasibility += this->m_low_bounds[j] - x;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case upper_bound:
        if (x > this->m_upper_bounds[j]) {
            this->m_costs[j] = 1;
            this->m_infeasibility += x - this->m_upper_bounds[j];
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case free_column:
        this->m_costs[j] = numeric_traits<T>::zero();
        break;
    default:
        SASSERT(false);
        break;
        }*/
}


// returns m_sign_of_alpha_r
int lar_core_solver::column_is_out_of_bounds(unsigned j) {
    /*
    switch (this->m_column_type[j]) {
    case fixed:
    case column_type::boxed:
        if (this->x_below_low_bound(j)) {
            return -1;
        }
        if (this->x_above_upper_bound(j)) {
            return 1;
        }
        return 0;
    case low_bound:
        if (this->x_below_low_bound(j)) {
            return -1;
        }
        return 0;
    case upper_bound:
        if (this->x_above_upper_bound(j)) {
            return 1;
        }
        return 0;
    default:
        return 0;
        break;
        }*/
    SASSERT(false);
    return true;
}



void lar_core_solver::calculate_pivot_row(unsigned i) {
    SASSERT(!m_r_solver.use_tableau());
    SASSERT(m_r_solver.m_pivot_row.is_OK());
    m_r_solver.m_pivot_row_of_B_1.clear();
    m_r_solver.m_pivot_row_of_B_1.resize(m_r_solver.m_m());
    m_r_solver.m_pivot_row.clear();
    m_r_solver.m_pivot_row.resize(m_r_solver.m_n());
    if (m_r_solver.m_settings.use_tableau()) {
        unsigned basis_j = m_r_solver.m_basis[i];
        for (auto & c : m_r_solver.m_A.m_rows[i]) {
            if (c.m_j != basis_j)
                m_r_solver.m_pivot_row.set_value(c.get_val(), c.m_j);
        }
        return;
    }

    m_r_solver.calculate_pivot_row_of_B_1(i);
    m_r_solver.calculate_pivot_row_when_pivot_row_of_B1_is_ready(i);
}



 void lar_core_solver::prefix_r() {
     if (!m_r_solver.m_settings.use_tableau()) {
        m_r_solver.m_copy_of_xB.resize(m_r_solver.m_n());
        m_r_solver.m_ed.resize(m_r_solver.m_m());
        m_r_solver.m_pivot_row.resize(m_r_solver.m_n()); 
        m_r_solver.m_pivot_row_of_B_1.resize(m_r_solver.m_m());
        m_r_solver.m_w.resize(m_r_solver.m_m());
        m_r_solver.m_y.resize(m_r_solver.m_m());
        m_r_solver.m_rows_nz.resize(m_r_solver.m_m(), 0);
        m_r_solver.m_columns_nz.resize(m_r_solver.m_n(), 0); 
        init_column_row_nz_for_r_solver();
    }

    m_r_solver.m_b.resize(m_r_solver.m_m());
    if (m_r_solver.m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows) {
        if(m_r_solver.m_settings.use_breakpoints_in_feasibility_search)
            m_r_solver.m_breakpoint_indices_queue.resize(m_r_solver.m_n());
        m_r_solver.m_costs.resize(m_r_solver.m_n());
        m_r_solver.m_d.resize(m_r_solver.m_n());
        m_r_solver.m_using_infeas_costs = true;
    }
}

 void lar_core_solver::prefix_d() {
    m_d_solver.m_b.resize(m_d_solver.m_m());
    m_d_solver.m_breakpoint_indices_queue.resize(m_d_solver.m_n());
    m_d_solver.m_copy_of_xB.resize(m_d_solver.m_n());
    m_d_solver.m_costs.resize(m_d_solver.m_n());
    m_d_solver.m_d.resize(m_d_solver.m_n());
    m_d_solver.m_ed.resize(m_d_solver.m_m());
    m_d_solver.m_pivot_row.resize(m_d_solver.m_n());
    m_d_solver.m_pivot_row_of_B_1.resize(m_d_solver.m_m());
    m_d_solver.m_w.resize(m_d_solver.m_m());
    m_d_solver.m_y.resize(m_d_solver.m_m());
    m_d_solver.m_steepest_edge_coefficients.resize(m_d_solver.m_n());
    m_d_solver.m_column_norms.clear();
    m_d_solver.m_column_norms.resize(m_d_solver.m_n(), 2);
    m_d_solver.m_inf_set.clear();
    m_d_solver.m_inf_set.resize(m_d_solver.m_n());
}

void lar_core_solver::fill_not_improvable_zero_sum_from_inf_row() {
    SASSERT(m_r_solver.A_mult_x_is_off() == false);
    unsigned bj = m_r_basis[m_r_solver.m_inf_row_index_for_tableau];
    m_infeasible_sum_sign =  m_r_solver.inf_sign_of_column(bj);
    m_infeasible_linear_combination.clear();
    for (auto & rc : m_r_solver.m_A.m_rows[m_r_solver.m_inf_row_index_for_tableau]) {
        m_infeasible_linear_combination.push_back(std::make_pair( rc.get_val(), rc.m_j));
    }
}

void lar_core_solver::fill_not_improvable_zero_sum() {
    if (m_r_solver.m_settings.simplex_strategy() == simplex_strategy_enum::tableau_rows) {
        fill_not_improvable_zero_sum_from_inf_row();
        return;
    }
    //  reusing the existing mechanism for row_feasibility_loop
    m_infeasible_sum_sign = m_r_solver.m_settings.use_breakpoints_in_feasibility_search? -1 : 1;
    m_infeasible_linear_combination.clear();
    for (auto j : m_r_solver.m_basis) {
        const mpq & cost_j = m_r_solver.m_costs[j];
        if (!numeric_traits<mpq>::is_zero(cost_j)) {
            m_infeasible_linear_combination.push_back(std::make_pair(cost_j, j));
        }
    }
    // m_costs are expressed by m_d ( additional costs), substructing the latter gives 0
    for (unsigned j = 0; j < m_r_solver.m_n(); j++) {
        if (m_r_solver.m_basis_heading[j] >= 0) continue;
        const mpq & d_j = m_r_solver.m_d[j];
        if (!numeric_traits<mpq>::is_zero(d_j)) {
            m_infeasible_linear_combination.push_back(std::make_pair(-d_j, j));
        }
    }
}


void lar_core_solver::solve() {
    SASSERT(m_r_solver.non_basic_columns_are_set_correctly());
    SASSERT(m_r_solver.inf_set_is_correct());
    if (m_r_solver.current_x_is_feasible() && m_r_solver.m_look_for_feasible_solution_only) {
        m_r_solver.set_status(OPTIMAL);
        return;
    }
    ++settings().st().m_need_to_solve_inf;
    SASSERT(!m_r_solver.A_mult_x_is_off());
    SASSERT((!settings().use_tableau()) || r_basis_is_OK());
    if (need_to_presolve_with_double_solver()) {
        prefix_d();
        lar_solution_signature solution_signature;
        vector<unsigned> changes_of_basis = find_solution_signature_with_doubles(solution_signature);
        if (m_d_solver.get_status() == TIME_EXHAUSTED) {
            m_r_solver.set_status(TIME_EXHAUSTED);
            return;
        }
        if (settings().use_tableau())
            solve_on_signature_tableau(solution_signature, changes_of_basis);
        else 
            solve_on_signature(solution_signature, changes_of_basis);
        SASSERT(!settings().use_tableau() || r_basis_is_OK());
    } else {
        if (!settings().use_tableau()) {
            bool snapped = m_r_solver.snap_non_basic_x_to_bound();   
            SASSERT(m_r_solver.non_basic_columns_are_set_correctly());
            if (snapped)
                m_r_solver.solve_Ax_eq_b();
        }
        if (m_r_solver.m_look_for_feasible_solution_only)
            m_r_solver.find_feasible_solution();
        else
            m_r_solver.solve();
        SASSERT(!settings().use_tableau() || r_basis_is_OK());
    }
    if (m_r_solver.get_status() == INFEASIBLE) {
        fill_not_improvable_zero_sum();
    } else if (m_r_solver.get_status() != UNBOUNDED) {
        m_r_solver.set_status(OPTIMAL);
    }
    SASSERT(r_basis_is_OK());
    SASSERT(m_r_solver.non_basic_columns_are_set_correctly());
    SASSERT(m_r_solver.inf_set_is_correct());
}


}

