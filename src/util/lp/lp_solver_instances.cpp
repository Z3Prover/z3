/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <string>
#include "util/lp/lp_solver.hpp"
template void lean::lp_solver<double, double>::add_constraint(lean::lp_relation, double, unsigned int);
template void lean::lp_solver<double, double>::cleanup();
template void lean::lp_solver<double, double>::count_slacks_and_artificials();
template void lean::lp_solver<double, double>::fill_m_b();
template void lean::lp_solver<double, double>::fill_matrix_A_and_init_right_side();
template void lean::lp_solver<double, double>::flip_costs();
template double lean::lp_solver<double, double>::get_column_cost_value(unsigned int, lean::column_info<double>*) const;
template int lean::lp_solver<double, double>::get_column_index_by_name(std::string) const;
template double lean::lp_solver<double, double>::get_column_value_with_core_solver(unsigned int, lean::lp_core_solver_base<double, double>*) const;
template lean::column_info<double>* lean::lp_solver<double, double>::get_or_create_column_info(unsigned int);
template void lean::lp_solver<double, double>::give_symbolic_name_to_column(std::string, unsigned int);
template void lean::lp_solver<double, double>::print_statistics_on_A(std::ostream & out);
template bool lean::lp_solver<double, double>::problem_is_empty();
template void lean::lp_solver<double, double>::scale();
template void lean::lp_solver<double, double>::set_scaled_cost(unsigned int);
template lean::lp_solver<double, double>::~lp_solver();
template void lean::lp_solver<lean::mpq, lean::mpq>::add_constraint(lean::lp_relation, lean::mpq, unsigned int);
template void lean::lp_solver<lean::mpq, lean::mpq>::cleanup();
template void lean::lp_solver<lean::mpq, lean::mpq>::count_slacks_and_artificials();
template void lean::lp_solver<lean::mpq, lean::mpq>::fill_m_b();
template void lean::lp_solver<lean::mpq, lean::mpq>::fill_matrix_A_and_init_right_side();
template void lean::lp_solver<lean::mpq, lean::mpq>::flip_costs();
template lean::mpq lean::lp_solver<lean::mpq, lean::mpq>::get_column_cost_value(unsigned int, lean::column_info<lean::mpq>*) const;
template int lean::lp_solver<lean::mpq, lean::mpq>::get_column_index_by_name(std::string) const;
template lean::mpq lean::lp_solver<lean::mpq, lean::mpq>::get_column_value_by_name(std::string) const;
template lean::mpq lean::lp_solver<lean::mpq, lean::mpq>::get_column_value_with_core_solver(unsigned int, lean::lp_core_solver_base<lean::mpq, lean::mpq>*) const;
template lean::column_info<lean::mpq>* lean::lp_solver<lean::mpq, lean::mpq>::get_or_create_column_info(unsigned int);
template void lean::lp_solver<lean::mpq, lean::mpq>::give_symbolic_name_to_column(std::string, unsigned int);
template void lean::lp_solver<lean::mpq, lean::mpq>::print_statistics_on_A(std::ostream & out);
template bool lean::lp_solver<lean::mpq, lean::mpq>::problem_is_empty();
template void lean::lp_solver<lean::mpq, lean::mpq>::scale();
template void lean::lp_solver<lean::mpq, lean::mpq>::set_scaled_cost(unsigned int);
template lean::lp_solver<lean::mpq, lean::mpq>::~lp_solver();
template double lean::lp_solver<double, double>::get_column_value_by_name(std::string) const;
