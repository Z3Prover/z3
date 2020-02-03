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
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include <functional>
#include "math/lp/lp_core_solver_base_def.h"
template bool lp::lp_core_solver_base<double, double>::A_mult_x_is_off() const;
template bool lp::lp_core_solver_base<double, double>::A_mult_x_is_off_on_index(const vector<unsigned> &) const;
template bool lp::lp_core_solver_base<double, double>::basis_heading_is_correct() const;
template void lp::lp_core_solver_base<double, double>::calculate_pivot_row_of_B_1(unsigned int);
template void lp::lp_core_solver_base<double, double>::calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned);
template bool lp::lp_core_solver_base<double, double>::column_is_dual_feasible(unsigned int) const;
template void lp::lp_core_solver_base<double, double>::fill_reduced_costs_from_m_y_by_rows();
template bool lp::lp_core_solver_base<double, double>::find_x_by_solving();
template lp::non_basic_column_value_position lp::lp_core_solver_base<double, double>::get_non_basic_column_value_position(unsigned int) const;
template lp::non_basic_column_value_position lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::get_non_basic_column_value_position(unsigned int) const;
template lp::non_basic_column_value_position lp::lp_core_solver_base<lp::mpq, lp::mpq>::get_non_basic_column_value_position(unsigned int) const;
template void lp::lp_core_solver_base<double, double>::init_reduced_costs_for_one_iteration();
template lp::lp_core_solver_base<double, double>::lp_core_solver_base(
    lp::static_matrix<double, double>&, vector<double>&, 
    vector<unsigned int >&,
    vector<unsigned> &, vector<int> &,
    vector<double >&, 
    vector<double >&, 
    lp::lp_settings&, const column_namer&, const vector<lp::column_type >&,
    const vector<double >&,
    const vector<double >&);

template bool lp::lp_core_solver_base<double, double>::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const*, std::ostream &);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const*, std::ostream &);
template void lp::lp_core_solver_base<double, double>::restore_x(unsigned int, double const&);
template void lp::lp_core_solver_base<double, double>::set_non_basic_x_to_correct_bounds();
template void lp::lp_core_solver_base<double, double>::snap_xN_to_bounds_and_free_columns_to_zeroes();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::snap_xN_to_bounds_and_free_columns_to_zeroes();
template void lp::lp_core_solver_base<double, double>::solve_Ax_eq_b();
template void lp::lp_core_solver_base<double, double>::solve_Bd(unsigned int);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq>>::solve_Bd(unsigned int, indexed_vector<lp::mpq>&);
template void lp::lp_core_solver_base<double, double>::solve_yB(vector<double >&);
template bool lp::lp_core_solver_base<double, double>::update_basis_and_x(int, int, double const&);
template void lp::lp_core_solver_base<double, double>::add_delta_to_entering(unsigned int, const double&);
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::A_mult_x_is_off() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::A_mult_x_is_off_on_index(const vector<unsigned> &) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::basis_heading_is_correct() const ;
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::calculate_pivot_row_of_B_1(unsigned int);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned);
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::column_is_dual_feasible(unsigned int) const;
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::fill_reduced_costs_from_m_y_by_rows();
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::find_x_by_solving();
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::init_reduced_costs_for_one_iteration();
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const*, std::ostream &);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::restore_x(unsigned int, lp::mpq const&);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::set_non_basic_x_to_correct_bounds();
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::solve_Ax_eq_b();
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::solve_Bd(unsigned int);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::solve_yB(vector<lp::mpq>&);
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::update_basis_and_x(int, int, lp::mpq const&);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::add_delta_to_entering(unsigned int, const lp::mpq&);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::calculate_pivot_row_of_B_1(unsigned int);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::init();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::init_basis_heading_and_non_basic_columns_vector();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::init_reduced_costs_for_one_iteration();
template lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::lp_core_solver_base(lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&, vector<lp::numeric_pair<lp::mpq> >&, vector<unsigned int >&, vector<unsigned> &, vector<int> &, vector<lp::numeric_pair<lp::mpq> >&, vector<lp::mpq>&, lp::lp_settings&, const column_namer&, const vector<lp::column_type >&,
                                                                                                   const vector<lp::numeric_pair<lp::mpq> >&,
                                                                                                   const vector<lp::numeric_pair<lp::mpq> >&);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::print_statistics_with_cost_and_check_that_the_time_is_over(lp::numeric_pair<lp::mpq>, std::ostream&);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::snap_xN_to_bounds_and_fill_xB();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_Ax_eq_b();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_Bd(unsigned int);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::update_basis_and_x(int, int, lp::numeric_pair<lp::mpq> const&);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::add_delta_to_entering(unsigned int, const lp::numeric_pair<lp::mpq>&);
template lp::lp_core_solver_base<lp::mpq, lp::mpq>::lp_core_solver_base(
                                                                              lp::static_matrix<lp::mpq, lp::mpq>&,
                                                                              vector<lp::mpq>&,
                                                                              vector<unsigned int >&,
                                                                              vector<unsigned> &, vector<int> &,
                                                                              vector<lp::mpq>&,
                                                                              vector<lp::mpq>&,
                                                                              lp::lp_settings&,
                                                                              const column_namer&,
                                                                              const vector<lp::column_type >&,
                                                                              const vector<lp::mpq>&,
                                                                              const vector<lp::mpq>&);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::print_statistics_with_iterations_and_check_that_the_time_is_over(std::ostream &);
template std::string lp::lp_core_solver_base<double, double>::column_name(unsigned int) const;
template void lp::lp_core_solver_base<double, double>::pretty_print(std::ostream & out);
template void lp::lp_core_solver_base<double, double>::restore_state(double*, double*);
template void lp::lp_core_solver_base<double, double>::save_state(double*, double*);
template std::string lp::lp_core_solver_base<lp::mpq, lp::mpq>::column_name(unsigned int) const;
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::pretty_print(std::ostream & out);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::restore_state(lp::mpq*, lp::mpq*);
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::save_state(lp::mpq*, lp::mpq*);
template std::string lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::column_name(unsigned int) const;
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::pretty_print(std::ostream & out);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::restore_state(lp::mpq*, lp::mpq*);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::save_state(lp::mpq*, lp::mpq*);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_yB(vector<lp::mpq>&);
template void lp::lp_core_solver_base<double, double>::init_lu();
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::init_lu();
template int lp::lp_core_solver_base<double, double>::pivots_in_column_and_row_are_different(int, int) const;
template int lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::pivots_in_column_and_row_are_different(int, int) const;
template int lp::lp_core_solver_base<lp::mpq, lp::mpq>::pivots_in_column_and_row_are_different(int, int) const;
template bool lp::lp_core_solver_base<double, double>::calc_current_x_is_feasible_include_non_basis(void)const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::calc_current_x_is_feasible_include_non_basis(void)const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::calc_current_x_is_feasible_include_non_basis() const;
template void  lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::pivot_fixed_vars_from_basis();
template bool lp::lp_core_solver_base<double, double>::column_is_feasible(unsigned int) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::column_is_feasible(unsigned int) const;
// template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::print_linear_combination_of_column_indices(vector<std::pair<lp::mpq, unsigned int>, std::allocator<std::pair<lp::mpq, unsigned int> > > const&, std::ostream&) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::column_is_feasible(unsigned int) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::snap_non_basic_x_to_bound();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::init_lu();
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::A_mult_x_is_off_on_index(vector<unsigned int> const&) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::find_x_by_solving();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::restore_x(unsigned int, lp::numeric_pair<lp::mpq> const&);
template bool lp::lp_core_solver_base<double, double>::pivot_for_tableau_on_basis();
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::pivot_for_tableau_on_basis();
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq>>::pivot_for_tableau_on_basis();
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq>>::pivot_column_tableau(unsigned int, unsigned int);
template bool lp::lp_core_solver_base<double, double>::pivot_column_tableau(unsigned int, unsigned int);
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::pivot_column_tableau(unsigned int, unsigned int);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::transpose_rows_tableau(unsigned int, unsigned int);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::inf_set_is_correct() const;
template bool lp::lp_core_solver_base<double, double>::inf_set_is_correct() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::inf_set_is_correct() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::infeasibility_costs_are_correct() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq >::infeasibility_costs_are_correct() const;
template bool lp::lp_core_solver_base<double, double >::infeasibility_costs_are_correct() const;
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::calculate_pivot_row(unsigned int);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::remove_from_basis(unsigned int);
