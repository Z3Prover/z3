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
#include "util/debug.h"
#include "util/lp/lu.hpp"
template double lp::dot_product<double, double>(vector<double> const&, vector<double> const&);
template lp::lu<double, double>::lu(lp::static_matrix<double, double> const&, vector<unsigned int>&, lp::lp_settings&);
template void lp::lu<double, double>::push_matrix_to_tail(lp::tail_matrix<double, double>*);
template void lp::lu<double, double>::replace_column(double, lp::indexed_vector<double>&, unsigned);
template void lp::lu<double, double>::solve_Bd(unsigned int, lp::indexed_vector<double>&, lp::indexed_vector<double>&);
template lp::lu<double, double>::~lu();
template void lp::lu<lp::mpq, lp::mpq>::push_matrix_to_tail(lp::tail_matrix<lp::mpq, lp::mpq>*);
template void lp::lu<lp::mpq, lp::mpq>::solve_Bd(unsigned int, lp::indexed_vector<lp::mpq>&, lp::indexed_vector<lp::mpq>&);
template lp::lu<lp::mpq, lp::mpq>::~lu();
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::push_matrix_to_tail(lp::tail_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >*);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_Bd(unsigned int, lp::indexed_vector<lp::mpq>&, lp::indexed_vector<lp::mpq>&);
template lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::~lu();
template lp::mpq lp::dot_product<lp::mpq, lp::mpq>(vector<lp::mpq > const&, vector<lp::mpq > const&);
template void lp::init_factorization<double, double>(lp::lu<double, double>*&, lp::static_matrix<double, double>&, vector<unsigned int>&, lp::lp_settings&);
template void lp::init_factorization<lp::mpq, lp::mpq>(lp::lu<lp::mpq, lp::mpq>*&, lp::static_matrix<lp::mpq, lp::mpq>&, vector<unsigned int>&, lp::lp_settings&);
template void lp::init_factorization<lp::mpq, lp::numeric_pair<lp::mpq> >(lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >*&, lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&, vector<unsigned int>&, lp::lp_settings&);
#ifdef Z3DEBUG
template void lp::print_matrix<double, double>(lp::sparse_matrix<double, double>&, std::ostream & out);
template void lp::print_matrix<lp::mpq, lp::mpq>(lp::static_matrix<lp::mpq, lp::mpq>&, std::ostream&);
template void lp::print_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >(lp::static_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&, std::ostream&);
template void lp::print_matrix<double, double>(lp::static_matrix<double, double>&, std::ostream & out);
template bool lp::lu<double, double>::is_correct(const vector<unsigned>& basis);
template bool lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::is_correct( vector<unsigned int> const &);
template lp::dense_matrix<double, double> lp::get_B<double, double>(lp::lu<double, double>&, const vector<unsigned>& basis);
template lp::dense_matrix<lp::mpq, lp::mpq> lp::get_B<lp::mpq, lp::mpq>(lp::lu<lp::mpq, lp::mpq>&, vector<unsigned int> const&);

#endif

template bool lp::lu<double, double>::pivot_the_row(int); // NOLINT
template void lp::lu<double, double>::init_vector_w(unsigned int, lp::indexed_vector<double>&);
template void lp::lu<double, double>::solve_By(vector<double>&);
template void lp::lu<double, double>::solve_By_when_y_is_ready_for_X(vector<double>&);
template void lp::lu<double, double>::solve_yB_with_error_check(vector<double>&, const vector<unsigned>& basis);
template void lp::lu<double, double>::solve_yB_with_error_check_indexed(lp::indexed_vector<double>&, vector<int> const&,  const vector<unsigned> & basis, const lp_settings&);
template void lp::lu<lp::mpq, lp::mpq>::replace_column(lp::mpq, lp::indexed_vector<lp::mpq>&, unsigned);
template void lp::lu<lp::mpq, lp::mpq>::solve_By(vector<lp::mpq >&);
template void lp::lu<lp::mpq, lp::mpq>::solve_By_when_y_is_ready_for_X(vector<lp::mpq >&);
template void lp::lu<lp::mpq, lp::mpq>::solve_yB_with_error_check(vector<lp::mpq >&, const vector<unsigned>& basis);
template void lp::lu<lp::mpq, lp::mpq>::solve_yB_with_error_check_indexed(lp::indexed_vector<lp::mpq>&, vector< int > const&,  const vector<unsigned> & basis, const lp_settings&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_yB_with_error_check_indexed(lp::indexed_vector<lp::mpq>&, vector< int > const&,  const vector<unsigned> & basis, const lp_settings&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::init_vector_w(unsigned int, lp::indexed_vector<lp::mpq>&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::replace_column(lp::mpq, lp::indexed_vector<lp::mpq>&, unsigned);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_Bd_faster(unsigned int, lp::indexed_vector<lp::mpq>&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_By(vector<lp::numeric_pair<lp::mpq> >&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_By_when_y_is_ready_for_X(vector<lp::numeric_pair<lp::mpq> >&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_yB_with_error_check(vector<lp::mpq >&, const vector<unsigned>& basis);
template void lp::lu<lp::mpq, lp::mpq>::solve_By(lp::indexed_vector<lp::mpq>&);
template void lp::lu<double, double>::solve_By(lp::indexed_vector<double>&);
template void lp::lu<double, double>::solve_yB_indexed(lp::indexed_vector<double>&);
template void lp::lu<lp::mpq, lp::mpq>::solve_yB_indexed(lp::indexed_vector<lp::mpq>&);
template void lp::lu<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_yB_indexed(lp::indexed_vector<lp::mpq>&);
template void lp::lu<lp::mpq, lp::mpq>::solve_By_for_T_indexed_only(lp::indexed_vector<lp::mpq>&, lp::lp_settings const&);
template void lp::lu<double, double>::solve_By_for_T_indexed_only(lp::indexed_vector<double>&, lp::lp_settings const&);
