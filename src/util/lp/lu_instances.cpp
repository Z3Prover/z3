/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include "util/debug.h"
#include "util/lp/lu.hpp"
template double lean::dot_product<double, double>(vector<double> const&, vector<double> const&);
template lean::lu<double, double>::lu(lean::static_matrix<double, double> const&, vector<unsigned int>&, lean::lp_settings&);
template void lean::lu<double, double>::push_matrix_to_tail(lean::tail_matrix<double, double>*);
template void lean::lu<double, double>::replace_column(double, lean::indexed_vector<double>&, unsigned);
template void lean::lu<double, double>::solve_Bd(unsigned int, lean::indexed_vector<double>&, lean::indexed_vector<double>&);
template lean::lu<double, double>::~lu();
template void lean::lu<lean::mpq, lean::mpq>::push_matrix_to_tail(lean::tail_matrix<lean::mpq, lean::mpq>*);
template void lean::lu<lean::mpq, lean::mpq>::solve_Bd(unsigned int, lean::indexed_vector<lean::mpq>&, lean::indexed_vector<lean::mpq>&);
template lean::lu<lean::mpq, lean::mpq>::~lu();
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::push_matrix_to_tail(lean::tail_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >*);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd(unsigned int, lean::indexed_vector<lean::mpq>&, lean::indexed_vector<lean::mpq>&);
template lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::~lu();
template lean::mpq lean::dot_product<lean::mpq, lean::mpq>(vector<lean::mpq > const&, vector<lean::mpq > const&);
template void lean::init_factorization<double, double>(lean::lu<double, double>*&, lean::static_matrix<double, double>&, vector<unsigned int>&, lean::lp_settings&);
template void lean::init_factorization<lean::mpq, lean::mpq>(lean::lu<lean::mpq, lean::mpq>*&, lean::static_matrix<lean::mpq, lean::mpq>&, vector<unsigned int>&, lean::lp_settings&);
template void lean::init_factorization<lean::mpq, lean::numeric_pair<lean::mpq> >(lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >*&, lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, vector<unsigned int>&, lean::lp_settings&);
#ifdef LEAN_DEBUG
template void lean::print_matrix<double, double>(lean::sparse_matrix<double, double>&, std::ostream & out);
template void lean::print_matrix<lean::mpq, lean::mpq>(lean::static_matrix<lean::mpq, lean::mpq>&, std::ostream&);
template void lean::print_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >(lean::static_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&, std::ostream&);
template void lean::print_matrix<double, double>(lean::static_matrix<double, double>&, std::ostream & out);
template bool lean::lu<double, double>::is_correct(const vector<unsigned>& basis);
template bool lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::is_correct( vector<unsigned int> const &);
template lean::dense_matrix<double, double> lean::get_B<double, double>(lean::lu<double, double>&, const vector<unsigned>& basis);
template lean::dense_matrix<lean::mpq, lean::mpq> lean::get_B<lean::mpq, lean::mpq>(lean::lu<lean::mpq, lean::mpq>&, vector<unsigned int> const&);

#endif

template bool lean::lu<double, double>::pivot_the_row(int); // NOLINT
template void lean::lu<double, double>::init_vector_w(unsigned int, lean::indexed_vector<double>&);
template void lean::lu<double, double>::solve_By(vector<double>&);
template void lean::lu<double, double>::solve_By_when_y_is_ready_for_X(vector<double>&);
template void lean::lu<double, double>::solve_yB_with_error_check(vector<double>&, const vector<unsigned>& basis);
template void lean::lu<double, double>::solve_yB_with_error_check_indexed(lean::indexed_vector<double>&, vector<int> const&,  const vector<unsigned> & basis, const lp_settings&);
template void lean::lu<lean::mpq, lean::mpq>::replace_column(lean::mpq, lean::indexed_vector<lean::mpq>&, unsigned);
template void lean::lu<lean::mpq, lean::mpq>::solve_By(vector<lean::mpq >&);
template void lean::lu<lean::mpq, lean::mpq>::solve_By_when_y_is_ready_for_X(vector<lean::mpq >&);
template void lean::lu<lean::mpq, lean::mpq>::solve_yB_with_error_check(vector<lean::mpq >&, const vector<unsigned>& basis);
template void lean::lu<lean::mpq, lean::mpq>::solve_yB_with_error_check_indexed(lean::indexed_vector<lean::mpq>&, vector< int > const&,  const vector<unsigned> & basis, const lp_settings&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB_with_error_check_indexed(lean::indexed_vector<lean::mpq>&, vector< int > const&,  const vector<unsigned> & basis, const lp_settings&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::init_vector_w(unsigned int, lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::replace_column(lean::mpq, lean::indexed_vector<lean::mpq>&, unsigned);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_Bd_faster(unsigned int, lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_By(vector<lean::numeric_pair<lean::mpq> >&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_By_when_y_is_ready_for_X(vector<lean::numeric_pair<lean::mpq> >&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB_with_error_check(vector<lean::mpq >&, const vector<unsigned>& basis);
template void lean::lu<lean::mpq, lean::mpq>::solve_By(lean::indexed_vector<lean::mpq>&);
template void lean::lu<double, double>::solve_By(lean::indexed_vector<double>&);
template void lean::lu<double, double>::solve_yB_indexed(lean::indexed_vector<double>&);
template void lean::lu<lean::mpq, lean::mpq>::solve_yB_indexed(lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::numeric_pair<lean::mpq> >::solve_yB_indexed(lean::indexed_vector<lean::mpq>&);
template void lean::lu<lean::mpq, lean::mpq>::solve_By_for_T_indexed_only(lean::indexed_vector<lean::mpq>&, lean::lp_settings const&);
template void lean::lu<double, double>::solve_By_for_T_indexed_only(lean::indexed_vector<double>&, lean::lp_settings const&);
