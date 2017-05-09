/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include <functional>
#include "util/lp/lp_core_solver_base.hpp"
template bool lean::lp_core_solver_base<double, double>::A_mult_x_is_off() const;
template bool lean::lp_core_solver_base<double, double>::A_mult_x_is_off_on_index(const vector<unsigned> &) const;
template bool lean::lp_core_solver_base<double, double>::basis_heading_is_correct() const;
template void lean::lp_core_solver_base<double, double>::calculate_pivot_row_of_B_1(unsigned int);
template void lean::lp_core_solver_base<double, double>::calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned);
template bool lean::lp_core_solver_base<double, double>::column_is_dual_feasible(unsigned int) const;
template void lean::lp_core_solver_base<double, double>::fill_reduced_costs_from_m_y_by_rows();
template bool lean::lp_core_solver_base<double, double>::find_x_by_solving();
template lean::non_basic_column_value_position lean::lp_core_solver_base<double, double>::get_non_basic_column_value_position(unsigned int) const;
template lean::non_basic_column_value_position lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::get_non_basic_column_value_position(unsigned int) const;
template lean::non_basic_column_value_position lean::lp_core_solver_base<lean::mpq, lean::mpq>::get_non_basic_column_value_position(unsigned int) const;
template void lean::lp_core_solver_base<double, double>::init_reduced_costs_for_one_iteration();
template lean::lp_core_solver_base<double, double>::lp_core_solver_base(
    lean::static_matrix<double, double>&, vector<double>&, 
    vector<unsigned int >&,
    vector<unsigned> &, vector<int> &,
    vector<double >&, 
    vector<double >&, 
    lean::lp_settings&, const column_namer&, const vector<lean::column_type >&,
    const vector<double >&,
    const vector<double >&);

template bool lean::lp_core_solver_base<double, double>::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const*, std::ostream &);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const*, std::ostream &);
template void lean::lp_core_solver_base<double, double>::restore_x(unsigned int, double const&);
template void lean::lp_core_solver_base<double, double>::set_non_basic_x_to_correct_bounds();
template void lean::lp_core_solver_base<double, double>::snap_xN_to_bounds_and_free_columns_to_zeroes();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::snap_xN_to_bounds_and_free_columns_to_zeroes();
template void lean::lp_core_solver_base<double, double>::solve_Ax_eq_b();
template void lean::lp_core_solver_base<double, double>::solve_Bd(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq>>::solve_Bd(unsigned int, indexed_vector<lean::mpq>&);
template void lean::lp_core_solver_base<double, double>::solve_yB(vector<double >&);
template bool lean::lp_core_solver_base<double, double>::update_basis_and_x(int, int, double const&);
template void lean::lp_core_solver_base<double, double>::update_x(unsigned int, const double&);
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::A_mult_x_is_off() const;
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::A_mult_x_is_off_on_index(const vector<unsigned> &) const;
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::basis_heading_is_correct() const ;
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::calculate_pivot_row_of_B_1(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned);
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::column_is_dual_feasible(unsigned int) const;
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::fill_reduced_costs_from_m_y_by_rows();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::find_x_by_solving();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::init_reduced_costs_for_one_iteration();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::print_statistics_with_iterations_and_nonzeroes_and_cost_and_check_that_the_time_is_over(char const*, std::ostream &);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::restore_x(unsigned int, lean::mpq const&);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::set_non_basic_x_to_correct_bounds();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::solve_Ax_eq_b();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::solve_Bd(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::solve_yB(vector<lean::mpq>&);
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::update_basis_and_x(int, int, lean::mpq const&);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::update_x(unsigned int, const lean::mpq&);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::calculate_pivot_row_of_B_1(unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::calculate_pivot_row_when_pivot_row_of_B1_is_ready(unsigned);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init_basis_heading_and_non_basic_columns_vector();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init_reduced_costs_for_one_iteration();
template lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::lp_core_solver_base(lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, vector<lean::numeric_pair<lean::mpq> >&, vector<unsigned int >&, vector<unsigned> &, vector<int> &, vector<lean::numeric_pair<lean::mpq> >&, vector<lean::mpq>&, lean::lp_settings&, const column_namer&, const vector<lean::column_type >&,
                                                                                                   const vector<lean::numeric_pair<lean::mpq> >&,
                                                                                                   const vector<lean::numeric_pair<lean::mpq> >&);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::print_statistics_with_cost_and_check_that_the_time_is_over(lean::numeric_pair<lean::mpq>, std::ostream&);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::snap_xN_to_bounds_and_fill_xB();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd(unsigned int);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::update_basis_and_x(int, int, lean::numeric_pair<lean::mpq> const&);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::update_x(unsigned int, const lean::numeric_pair<lean::mpq>&);
template lean::lp_core_solver_base<lean::mpq, lean::mpq>::lp_core_solver_base(
                                                                              lean::static_matrix<lean::mpq, lean::mpq>&,
                                                                              vector<lean::mpq>&,
                                                                              vector<unsigned int >&,
                                                                              vector<unsigned> &, vector<int> &,
                                                                              vector<lean::mpq>&,
                                                                              vector<lean::mpq>&,
                                                                              lean::lp_settings&,
                                                                              const column_namer&,
                                                                              const vector<lean::column_type >&,
                                                                              const vector<lean::mpq>&,
                                                                              const vector<lean::mpq>&);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::print_statistics_with_iterations_and_check_that_the_time_is_over(std::ostream &);
template std::string lean::lp_core_solver_base<double, double>::column_name(unsigned int) const;
template void lean::lp_core_solver_base<double, double>::pretty_print(std::ostream & out);
template void lean::lp_core_solver_base<double, double>::restore_state(double*, double*);
template void lean::lp_core_solver_base<double, double>::save_state(double*, double*);
template std::string lean::lp_core_solver_base<lean::mpq, lean::mpq>::column_name(unsigned int) const;
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::pretty_print(std::ostream & out);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::restore_state(lean::mpq*, lean::mpq*);
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::save_state(lean::mpq*, lean::mpq*);
template std::string lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::column_name(unsigned int) const;
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::pretty_print(std::ostream & out);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::restore_state(lean::mpq*, lean::mpq*);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::save_state(lean::mpq*, lean::mpq*);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB(vector<lean::mpq>&);
template void lean::lp_core_solver_base<double, double>::init_lu();
template void lean::lp_core_solver_base<lean::mpq, lean::mpq>::init_lu();
template int lean::lp_core_solver_base<double, double>::pivots_in_column_and_row_are_different(int, int) const;
template int lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::pivots_in_column_and_row_are_different(int, int) const;
template int lean::lp_core_solver_base<lean::mpq, lean::mpq>::pivots_in_column_and_row_are_different(int, int) const;
template bool lean::lp_core_solver_base<double, double>::calc_current_x_is_feasible_include_non_basis(void)const;
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::calc_current_x_is_feasible_include_non_basis(void)const;
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::calc_current_x_is_feasible_include_non_basis() const;
template void  lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::pivot_fixed_vars_from_basis();
template bool lean::lp_core_solver_base<double, double>::column_is_feasible(unsigned int) const;
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::column_is_feasible(unsigned int) const;
// template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::print_linear_combination_of_column_indices(vector<std::pair<lean::mpq, unsigned int>, std::allocator<std::pair<lean::mpq, unsigned int> > > const&, std::ostream&) const;
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::column_is_feasible(unsigned int) const;
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::snap_non_basic_x_to_bound();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::init_lu();
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::A_mult_x_is_off_on_index(vector<unsigned int> const&) const;
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::find_x_by_solving();
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::restore_x(unsigned int, lean::numeric_pair<lean::mpq> const&);
template bool lean::lp_core_solver_base<double, double>::pivot_for_tableau_on_basis();
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::pivot_for_tableau_on_basis();
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq>>::pivot_for_tableau_on_basis();
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq>>::pivot_column_tableau(unsigned int, unsigned int);
template bool lean::lp_core_solver_base<double, double>::pivot_column_tableau(unsigned int, unsigned int);
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::pivot_column_tableau(unsigned int, unsigned int);
template void lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::transpose_rows_tableau(unsigned int, unsigned int);
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::inf_set_is_correct() const;
template bool lean::lp_core_solver_base<double, double>::inf_set_is_correct() const;
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq>::inf_set_is_correct() const;
template bool lean::lp_core_solver_base<lean::mpq, lean::numeric_pair<lean::mpq> >::infeasibility_costs_are_correct() const;
template bool lean::lp_core_solver_base<lean::mpq, lean::mpq >::infeasibility_costs_are_correct() const;
template bool lean::lp_core_solver_base<double, double >::infeasibility_costs_are_correct() const;
