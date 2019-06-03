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
#include "math/lp/lp_solver_def.h"
template void lp::lp_solver<double, double>::add_constraint(lp::lp_relation, double, unsigned int);
template void lp::lp_solver<double, double>::cleanup();
template void lp::lp_solver<double, double>::count_slacks_and_artificials();
template void lp::lp_solver<double, double>::fill_m_b();
template void lp::lp_solver<double, double>::fill_matrix_A_and_init_right_side();
template void lp::lp_solver<double, double>::flip_costs();
template double lp::lp_solver<double, double>::get_column_cost_value(unsigned int, lp::column_info<double>*) const;
template int lp::lp_solver<double, double>::get_column_index_by_name(std::string) const;
template double lp::lp_solver<double, double>::get_column_value_with_core_solver(unsigned int, lp::lp_core_solver_base<double, double>*) const;
template lp::column_info<double>* lp::lp_solver<double, double>::get_or_create_column_info(unsigned int);
template void lp::lp_solver<double, double>::give_symbolic_name_to_column(std::string, unsigned int);
template void lp::lp_solver<double, double>::print_statistics_on_A(std::ostream & out);
template bool lp::lp_solver<double, double>::problem_is_empty();
template void lp::lp_solver<double, double>::scale();
template void lp::lp_solver<double, double>::set_scaled_cost(unsigned int);
template lp::lp_solver<double, double>::~lp_solver();
template void lp::lp_solver<lp::mpq, lp::mpq>::add_constraint(lp::lp_relation, lp::mpq, unsigned int);
template void lp::lp_solver<lp::mpq, lp::mpq>::cleanup();
template void lp::lp_solver<lp::mpq, lp::mpq>::count_slacks_and_artificials();
template void lp::lp_solver<lp::mpq, lp::mpq>::fill_m_b();
template void lp::lp_solver<lp::mpq, lp::mpq>::fill_matrix_A_and_init_right_side();
template void lp::lp_solver<lp::mpq, lp::mpq>::flip_costs();
template lp::mpq lp::lp_solver<lp::mpq, lp::mpq>::get_column_cost_value(unsigned int, lp::column_info<lp::mpq>*) const;
template int lp::lp_solver<lp::mpq, lp::mpq>::get_column_index_by_name(std::string) const;
template lp::mpq lp::lp_solver<lp::mpq, lp::mpq>::get_column_value_by_name(std::string) const;
template lp::mpq lp::lp_solver<lp::mpq, lp::mpq>::get_column_value_with_core_solver(unsigned int, lp::lp_core_solver_base<lp::mpq, lp::mpq>*) const;
template lp::column_info<lp::mpq>* lp::lp_solver<lp::mpq, lp::mpq>::get_or_create_column_info(unsigned int);
template void lp::lp_solver<lp::mpq, lp::mpq>::give_symbolic_name_to_column(std::string, unsigned int);
template void lp::lp_solver<lp::mpq, lp::mpq>::print_statistics_on_A(std::ostream & out);
template bool lp::lp_solver<lp::mpq, lp::mpq>::problem_is_empty();
template void lp::lp_solver<lp::mpq, lp::mpq>::scale();
template void lp::lp_solver<lp::mpq, lp::mpq>::set_scaled_cost(unsigned int);
template lp::lp_solver<lp::mpq, lp::mpq>::~lp_solver();
template double lp::lp_solver<double, double>::get_column_value_by_name(std::string) const;
