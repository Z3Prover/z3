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
#include "math/lp/lar_core_solver.h"
#include "math/lp/lar_solution_signature.h"
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
                    m_r_lower_bounds(),
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
                    m_d_lower_bounds,
                    m_d_upper_bounds,
                    settings,
                    column_names){}

void lar_core_solver::init_costs(bool first_time) {
    lp_assert(false); // should not be called
    // lp_assert(this->m_x.size() >= this->m_n());
    // lp_assert(this->m_column_types.size() >= this->m_n());
    // if (first_time)
    //     this->m_costs.resize(this->m_n());
    // X inf = this->m_infeasibility;
    // this->m_infeasibility = zero_of_type<X>();
    // for (unsigned j = this->m_n(); j--;)
    //     init_cost_for_column(j);
    // if (!(first_time || inf >= this->m_infeasibility)) {
    //     LP_OUT(this->m_settings, "iter = " << this->total_iterations() << std::endl);
    //     LP_OUT(this->m_settings, "inf was " << T_to_string(inf) << " and now " << T_to_string(this->m_infeasibility) << std::endl);
    //     lp_assert(false);
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
        } else if (x < this->m_lower_bounds[j]) {
            this->m_infeasibility += this->m_lower_bounds[j] - x;
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case lower_bound:
        if (x < this->m_lower_bounds[j]) {
            this->m_costs[j] = -1;
            this->m_infeasibility += this->m_lower_bounds[j] - x;
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
        lp_assert(false);
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
    case lower_bound:
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
    lp_assert(false);
    return true;
}



void lar_core_solver::calculate_pivot_row(unsigned i) {
    m_r_solver.calculate_pivot_row(i);
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
    CASSERT("A_off", m_r_solver.A_mult_x_is_off() == false);
    unsigned bj = m_r_basis[m_r_solver.m_inf_row_index_for_tableau];
    m_infeasible_sum_sign =  m_r_solver.inf_sign_of_column(bj);
    m_infeasible_linear_combination.clear();
    for (auto & rc : m_r_solver.m_A.m_rows[m_r_solver.m_inf_row_index_for_tableau]) {
        m_infeasible_linear_combination.push_back(std::make_pair( rc.get_val(), rc.var()));
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

unsigned lar_core_solver::get_number_of_non_ints() const {
	unsigned n = 0;
	for (auto & x : m_r_solver.m_x) {
		if (x.is_int() == false)
			n++;
	}
	return n;
}

void lar_core_solver::solve() {
    TRACE("lar_solver", tout << m_r_solver.get_status() << "\n";);
    lp_assert(m_r_solver.non_basic_columns_are_set_correctly());
    lp_assert(m_r_solver.inf_set_is_correct());
	TRACE("find_feas_stats", tout << "infeasibles = " << m_r_solver.m_inf_set.size() << ", int_infs = " << get_number_of_non_ints() << std::endl;);
	if (m_r_solver.current_x_is_feasible() && m_r_solver.m_look_for_feasible_solution_only) {
            m_r_solver.set_status(lp_status::OPTIMAL);
            TRACE("lar_solver", tout << m_r_solver.get_status() << "\n";);
            return;
	}
    ++settings().stats().m_need_to_solve_inf;
    CASSERT("A_off", !m_r_solver.A_mult_x_is_off());
    lp_assert((!settings().use_tableau()) || r_basis_is_OK());
    if (need_to_presolve_with_double_solver()) {
        TRACE("lar_solver", tout << "presolving\n";);
        prefix_d();
        lar_solution_signature solution_signature;
        vector<unsigned> changes_of_basis = find_solution_signature_with_doubles(solution_signature);
        if (m_d_solver.get_status() == lp_status::TIME_EXHAUSTED) {
            m_r_solver.set_status(lp_status::TIME_EXHAUSTED);
            return;
        }
        if (settings().use_tableau())
            solve_on_signature_tableau(solution_signature, changes_of_basis);
        else 
            solve_on_signature(solution_signature, changes_of_basis);

        lp_assert(!settings().use_tableau() || r_basis_is_OK());
    } else {
        if (!settings().use_tableau()) {
            TRACE("lar_solver", tout << "no tablau\n";);
            bool snapped = m_r_solver.snap_non_basic_x_to_bound();   
            lp_assert(m_r_solver.non_basic_columns_are_set_correctly());
            if (snapped)
                m_r_solver.solve_Ax_eq_b();
        }
        if (m_r_solver.m_look_for_feasible_solution_only) //todo : should it be set?
            m_r_solver.find_feasible_solution();
        else {
            m_r_solver.solve();
        }
        lp_assert(!settings().use_tableau() || r_basis_is_OK());
    }
    if (m_r_solver.get_status() == lp_status::INFEASIBLE) {
        fill_not_improvable_zero_sum();
    } else if (m_r_solver.get_status() != lp_status::UNBOUNDED) {
        m_r_solver.set_status(lp_status::OPTIMAL);
    }
    lp_assert(r_basis_is_OK());
    lp_assert(m_r_solver.non_basic_columns_are_set_correctly());
    lp_assert(m_r_solver.inf_set_is_correct());

    TRACE("lar_solver", tout << m_r_solver.get_status() << "\n";);
}


}

