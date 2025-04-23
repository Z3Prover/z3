/*++
Copyright (c) 2017 Microsoft Corporation

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once

#include <string>
#include "util/vector.h"
#include "math/lp/lar_core_solver.h"
namespace lp {
lar_core_solver::lar_core_solver(
    lp_settings & settings,
    const column_namer & column_names):
    m_infeasible_sum_sign(0),
    m_r_solver(m_r_A,
               m_right_sides_dummy,
               m_r_x,
               m_r_basis,
               m_r_nbasis,
               m_r_heading,
               m_costs_dummy,
               m_column_types(),
               m_r_lower_bounds,
               m_r_upper_bounds,
               settings,
               column_names) {
}    
    

void lar_core_solver::prefix_r() {
    
    // m_r_solver.m_b.resize(m_r_solver.m_m());
    if (m_r_solver.m_settings.simplex_strategy() != simplex_strategy_enum::tableau_rows) {
        m_r_solver.m_costs.resize(m_r_solver.m_n());
        m_r_solver.m_d.resize(m_r_solver.m_n());
    }
}


void lar_core_solver::fill_not_improvable_zero_sum_from_inf_row() {
    unsigned bj = m_r_basis[m_r_solver.m_inf_row_index_for_tableau];
    m_infeasible_sum_sign =  m_r_solver.inf_sign_of_column(bj);
    m_infeasible_linear_combination.clear();
    for (auto & rc : m_r_solver.m_A.m_rows[m_r_solver.m_inf_row_index_for_tableau]) 
        m_infeasible_linear_combination.push_back({rc.coeff(), rc.var()});
}

void lar_core_solver::fill_not_improvable_zero_sum() {
    if (m_r_solver.m_settings.simplex_strategy() == simplex_strategy_enum::tableau_rows) {
        fill_not_improvable_zero_sum_from_inf_row();
        return;
    }
    //  reusing the existing mechanism for row_feasibility_loop
    m_infeasible_sum_sign = 1;
    m_infeasible_linear_combination.clear();
    for (auto j : m_r_solver.m_basis) {
        const mpq & cost_j = m_r_solver.m_costs[j];
        if (!numeric_traits<mpq>::is_zero(cost_j)) 
            m_infeasible_linear_combination.push_back(std::make_pair(cost_j, j));        
    }
    // m_costs are expressed by m_d ( additional costs), substructing the latter gives 0
    for (unsigned j = 0; j < m_r_solver.m_n(); j++) {
        if (m_r_solver.m_basis_heading[j] >= 0) continue;
        const mpq & d_j = m_r_solver.m_d[j];
        if (!numeric_traits<mpq>::is_zero(d_j)) 
            m_infeasible_linear_combination.push_back(std::make_pair(-d_j, j));        
    }
}

unsigned lar_core_solver::get_number_of_non_ints() const {
    unsigned n = 0;
    for (auto & x : r_x()) 
        if (!x.is_int())
            n++;    
    return n;
}

void lar_core_solver::solve() {
    TRACE("lar_solver", tout << m_r_solver.get_status() << "\n";);
    SASSERT(m_r_solver.non_basic_columns_are_set_correctly());
    SASSERT(m_r_solver.inf_heap_is_correct());
	TRACE("find_feas_stats", tout << "infeasibles = " << m_r_solver.inf_heap_size() << ", int_infs = " << get_number_of_non_ints() << std::endl;);
	if (m_r_solver.current_x_is_feasible() && m_r_solver.m_look_for_feasible_solution_only) {
        m_r_solver.set_status(lp_status::OPTIMAL);
        TRACE("lar_solver", tout << m_r_solver.get_status() << "\n";);
        return;
	}
    ++m_r_solver.m_settings.stats().m_need_to_solve_inf;
    SASSERT( r_basis_is_OK());
             
    if (m_r_solver.m_look_for_feasible_solution_only) //todo : should it be set?
         m_r_solver.find_feasible_solution();
    else 
        m_r_solver.solve();
    
    SASSERT(r_basis_is_OK());
    
    switch (m_r_solver.get_status())
    {
    case lp_status::INFEASIBLE:
        fill_not_improvable_zero_sum();
        break;
    case lp_status::CANCELLED:
    case lp_status::UNBOUNDED: // do nothing in these cases
        break;
    default:  // adjust the status to optimal
        m_r_solver.set_status(lp_status::OPTIMAL);
        break;
    }
    SASSERT(r_basis_is_OK());
    SASSERT(m_r_solver.non_basic_columns_are_set_correctly());
    SASSERT(m_r_solver.inf_heap_is_correct());

  TRACE("lar_solver", tout << m_r_solver.get_status() << "\n";);
}

} // namespace lp
