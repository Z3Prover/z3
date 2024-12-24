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
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::basis_heading_is_correct() const ;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::column_is_dual_feasible(unsigned int) const;
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::add_delta_to_entering(unsigned int, const lp::mpq&);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::init();
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::init_basis_heading_and_non_basic_columns_vector();
template lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::lp_core_solver_base(lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&, 
    // vector<lp::numeric_pair<lp::mpq> >&, 
    vector<unsigned int >&, vector<unsigned> &, std_vector<int> &, vector<lp::numeric_pair<lp::mpq> >&, vector<lp::mpq>&, lp::lp_settings&, const column_namer&, const vector<lp::column_type >&,
                                                                                                   const vector<lp::numeric_pair<lp::mpq> >&,
                                                                                                   const vector<lp::numeric_pair<lp::mpq> >&);

template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::add_delta_to_entering(unsigned int, const lp::numeric_pair<lp::mpq>&);
template lp::lp_core_solver_base<lp::mpq, lp::mpq>::lp_core_solver_base(
                                                                              lp::static_matrix<lp::mpq, lp::mpq>&,
                                                                              //vector<lp::mpq>&,
                                                                              vector<unsigned int >&,
                                                                              vector<unsigned> &,
                                                                              std_vector<int> &,
                                                                              vector<lp::mpq>&,
                                                                              vector<lp::mpq>&,
                                                                              lp::lp_settings&,
                                                                              const column_namer&,
                                                                              const vector<lp::column_type >&,
                                                                              const vector<lp::mpq>&,
                                                                              const vector<lp::mpq>&);
template std::string lp::lp_core_solver_base<lp::mpq, lp::mpq>::column_name(unsigned int) const;
template void lp::lp_core_solver_base<lp::mpq, lp::mpq>::pretty_print(std::ostream & out);
template std::string lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::column_name(unsigned int) const;
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::pretty_print(std::ostream & out);
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::calc_current_x_is_feasible_include_non_basis(void)const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::calc_current_x_is_feasible_include_non_basis() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::column_is_feasible(unsigned int) const;
// template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::print_linear_combination_of_column_indices(vector<std::pair<lp::mpq, unsigned int>, std::allocator<std::pair<lp::mpq, unsigned int> > > const&, std::ostream&) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::column_is_feasible(unsigned int) const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq>>::pivot_column_tableau(unsigned int, unsigned int);
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::pivot_column_tableau(unsigned int, unsigned int);
template void lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::transpose_rows_tableau(unsigned int, unsigned int);
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::inf_heap_is_correct() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::mpq>::inf_heap_is_correct() const;
template bool lp::lp_core_solver_base<lp::mpq, lp::numeric_pair<lp::mpq> >::remove_from_basis_core(unsigned int, unsigned int);


