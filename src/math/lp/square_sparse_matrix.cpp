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
#include <memory>
#include "util/vector.h"
#include "math/lp/lp_settings.h"
#include "math/lp/lu.h"
#include "math/lp/square_sparse_matrix_def.h"
#include "math/lp/dense_matrix.h"
namespace lp {
template double square_sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, vector<double> const&) const;
template void square_sparse_matrix<double, double>::add_new_element(unsigned int, unsigned int, const double&);
template void square_sparse_matrix<double, double>::divide_row_by_constant(unsigned int, const double&, lp_settings&);
template bool square_sparse_matrix<double, double>::fill_eta_matrix(unsigned int, eta_matrix<double, double>**);
template const double & square_sparse_matrix<double, double>::get(unsigned int, unsigned int) const;
template unsigned square_sparse_matrix<double, double>::get_number_of_nonzeroes() const;
template bool square_sparse_matrix<double, double>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned square_sparse_matrix<double, double>::lowest_row_in_column(unsigned int);
template bool square_sparse_matrix<double, double>::pivot_row_to_row(unsigned int, const double&, unsigned int, lp_settings&);
template bool square_sparse_matrix<double, double>::pivot_with_eta(unsigned int, eta_matrix<double, double>*, lp_settings&);
template void square_sparse_matrix<double, double>::prepare_for_factorization();
template void square_sparse_matrix<double, double>::remove_element(vector<indexed_value<double> >&, indexed_value<double>&);
template void     square_sparse_matrix<double, double>::replace_column(unsigned int, indexed_vector<double>&, lp_settings&);
template void     square_sparse_matrix<double, double>::set(unsigned int, unsigned int, double);
template void     square_sparse_matrix<double, double>::set_max_in_row(vector<indexed_value<double> >&);
template bool square_sparse_matrix<double, double>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<double>&, lp_settings&);
template bool square_sparse_matrix<double, double>::shorten_active_matrix(unsigned int, eta_matrix<double, double>*);
template void square_sparse_matrix<double, double>::solve_y_U(vector<double>&) const;
template square_sparse_matrix<double, double>::square_sparse_matrix(unsigned int, unsigned);
template void     square_sparse_matrix<mpq, mpq>::add_new_element(unsigned int, unsigned int, const mpq&);
template void     square_sparse_matrix<mpq, mpq>::divide_row_by_constant(unsigned int, const mpq&, lp_settings&);
template bool square_sparse_matrix<mpq, mpq>::fill_eta_matrix(unsigned int, eta_matrix<mpq, mpq>**);
template  mpq const & square_sparse_matrix<mpq, mpq>::get(unsigned int, unsigned int) const;
template unsigned square_sparse_matrix<mpq, mpq>::get_number_of_nonzeroes() const;
template bool square_sparse_matrix<mpq, mpq>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned square_sparse_matrix<mpq, mpq>::lowest_row_in_column(unsigned int);
template bool square_sparse_matrix<mpq, mpq>::pivot_with_eta(unsigned int, eta_matrix<mpq, mpq>*, lp_settings&);
template void  square_sparse_matrix<mpq, mpq>::prepare_for_factorization();
template void   square_sparse_matrix<mpq, mpq>::remove_element(vector<indexed_value<mpq>> &, indexed_value<mpq>&);
template void     square_sparse_matrix<mpq, mpq>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     square_sparse_matrix<mpq, mpq>::set_max_in_row(vector<indexed_value<mpq>>&);
template bool square_sparse_matrix<mpq, mpq>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool square_sparse_matrix<mpq, mpq>::shorten_active_matrix(unsigned int, eta_matrix<mpq, mpq>*);
template void     square_sparse_matrix<mpq, mpq>::solve_y_U(vector<mpq>&) const;
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::add_new_element(unsigned int, unsigned int, const mpq&);
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::divide_row_by_constant(unsigned int, const mpq&, lp_settings&);
template bool square_sparse_matrix<mpq, numeric_pair<mpq>>::fill_eta_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >**);
template const mpq & square_sparse_matrix<mpq, numeric_pair<mpq>>::get(unsigned int, unsigned int) const;
template unsigned square_sparse_matrix<mpq, numeric_pair<mpq>>::get_number_of_nonzeroes() const;
template bool square_sparse_matrix<mpq, numeric_pair<mpq>>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned square_sparse_matrix<mpq, numeric_pair<mpq>>::lowest_row_in_column(unsigned int);
template bool square_sparse_matrix<mpq, numeric_pair<mpq>>::pivot_with_eta(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*, lp_settings&);
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::prepare_for_factorization();
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::remove_element(vector<indexed_value<mpq>>&, indexed_value<mpq>&);
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::set_max_in_row(vector<indexed_value<mpq>>&);
template bool square_sparse_matrix<mpq, numeric_pair<mpq>>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool     square_sparse_matrix<mpq, numeric_pair<mpq>>::shorten_active_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*);
template void     square_sparse_matrix<mpq, numeric_pair<mpq>>::solve_y_U(vector<mpq>&) const;
template void square_sparse_matrix<double, double>::double_solve_U_y<double>(indexed_vector<double>&, const lp_settings  &);
template void square_sparse_matrix<mpq, mpq>::double_solve_U_y<mpq>(indexed_vector<mpq>&, const lp_settings&);
template void square_sparse_matrix<mpq, numeric_pair<mpq>>::double_solve_U_y<mpq>(indexed_vector<mpq>&, const lp_settings&);
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::double_solve_U_y<numeric_pair<mpq> >(indexed_vector<numeric_pair<mpq>>&, const lp_settings&);
template void square_sparse_matrix<double, double>::solve_U_y_indexed_only<double>(indexed_vector<double>&, const lp_settings&, vector<unsigned> &);
template void square_sparse_matrix<mpq, mpq>::solve_U_y_indexed_only<mpq>(indexed_vector<mpq>&, const lp_settings &, vector<unsigned> &);
#ifdef Z3DEBUG
template bool square_sparse_matrix<double, double>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool square_sparse_matrix<mpq, mpq>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool square_sparse_matrix<mpq, numeric_pair<mpq> >::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
#endif

template void square_sparse_matrix<mpq, numeric_pair<mpq> >::solve_U_y_indexed_only<mpq>(indexed_vector<mpq>&, const lp_settings &, vector<unsigned> &);
template void square_sparse_matrix<mpq, mpq>::solve_U_y<mpq>(vector<mpq>&);
template void square_sparse_matrix<mpq, mpq>::double_solve_U_y<mpq>(vector<mpq >&);
template void square_sparse_matrix<double, double>::solve_U_y<double>(vector<double>&);
template void square_sparse_matrix<double, double>::double_solve_U_y<double>(vector<double>&);
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::solve_U_y<numeric_pair<mpq> >(vector<numeric_pair<mpq> >&);
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::double_solve_U_y<numeric_pair<mpq> >(vector<numeric_pair<mpq> >&);
template void square_sparse_matrix<double, double>::find_error_in_solution_U_y_indexed<double>(indexed_vector<double>&, indexed_vector<double>&, const vector<unsigned> &);
template double square_sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, indexed_vector<double> const&) const;
template void square_sparse_matrix<mpq, mpq>::find_error_in_solution_U_y_indexed<mpq>(indexed_vector<mpq>&, indexed_vector<mpq>&, const vector<unsigned> &);
template mpq square_sparse_matrix<mpq, mpq>::dot_product_with_row<mpq>(unsigned int, indexed_vector<mpq> const&) const;
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::find_error_in_solution_U_y_indexed<mpq>(indexed_vector<mpq>&, indexed_vector<mpq>&, const vector<unsigned> &);
template mpq square_sparse_matrix<mpq, numeric_pair<mpq> >::dot_product_with_row<mpq>(unsigned int, indexed_vector<mpq> const&) const;
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::find_error_in_solution_U_y_indexed<numeric_pair<mpq> >(indexed_vector<numeric_pair<mpq> >&, indexed_vector<numeric_pair<mpq> >&, const vector<unsigned> &);
template numeric_pair<mpq> square_sparse_matrix<mpq, numeric_pair<mpq> >::dot_product_with_row<numeric_pair<mpq> >(unsigned int, indexed_vector<numeric_pair<mpq> > const&) const;
template void square_sparse_matrix<mpq, mpq>::extend_and_sort_active_rows(vector<unsigned int> const&, vector<unsigned int>&);

template void square_sparse_matrix<mpq, numeric_pair<mpq> >::extend_and_sort_active_rows(vector<unsigned int> const&, vector<unsigned int>&);

template void square_sparse_matrix<mpq, numeric_pair<mpq> >::solve_U_y<mpq>(vector<mpq >&);
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::double_solve_U_y<mpq>(vector<mpq >&);
template void square_sparse_matrix< mpq,numeric_pair< mpq> >::set(unsigned int,unsigned int, mpq);
template void square_sparse_matrix<double, double>::solve_y_U_indexed(indexed_vector<double>&, const lp_settings & );
template void square_sparse_matrix<mpq, mpq>::solve_y_U_indexed(indexed_vector<mpq>&, const lp_settings &);
template void square_sparse_matrix<mpq, numeric_pair<mpq> >::solve_y_U_indexed(indexed_vector<mpq>&, const lp_settings &);

template square_sparse_matrix<double, double>::square_sparse_matrix(static_matrix<double, double> const&, vector<unsigned int, true, unsigned int>&);
template square_sparse_matrix<mpq, mpq>::square_sparse_matrix (static_matrix<mpq, mpq> const&, vector<unsigned int, true, unsigned int>&);
template square_sparse_matrix<mpq, numeric_pair<mpq> >::square_sparse_matrix(static_matrix<mpq, numeric_pair<mpq> > const&, vector<unsigned int, true, unsigned int>&);
}
template void lp::square_sparse_matrix<double, double>::copy_from_input_on_basis<lp::static_matrix<double, double> >(lp::static_matrix<double, double> const&, vector<unsigned int, true, unsigned int>&);
template void lp::square_sparse_matrix<rational, rational>::copy_from_input_on_basis<lp::static_matrix<rational, rational> >(lp::static_matrix<rational, rational> const&, vector<unsigned int, true, unsigned int>&);
