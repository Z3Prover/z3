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
#include "util/lp/lp_settings.h"
#include "util/lp/lu.h"
#include "util/lp/sparse_matrix.hpp"
#include "util/lp/dense_matrix.h"
namespace lp {
template double sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, vector<double> const&) const;
template void sparse_matrix<double, double>::add_new_element(unsigned int, unsigned int, const double&);
template void sparse_matrix<double, double>::divide_row_by_constant(unsigned int, const double&, lp_settings&);
template bool sparse_matrix<double, double>::fill_eta_matrix(unsigned int, eta_matrix<double, double>**);
template const double & sparse_matrix<double, double>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<double, double>::get_number_of_nonzeroes() const;
template bool sparse_matrix<double, double>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned sparse_matrix<double, double>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<double, double>::pivot_row_to_row(unsigned int, const double&, unsigned int, lp_settings&);
template bool sparse_matrix<double, double>::pivot_with_eta(unsigned int, eta_matrix<double, double>*, lp_settings&);
template void sparse_matrix<double, double>::prepare_for_factorization();
template void sparse_matrix<double, double>::remove_element(vector<indexed_value<double> >&, indexed_value<double>&);
template void     sparse_matrix<double, double>::replace_column(unsigned int, indexed_vector<double>&, lp_settings&);
template void     sparse_matrix<double, double>::set(unsigned int, unsigned int, double);
template void     sparse_matrix<double, double>::set_max_in_row(vector<indexed_value<double> >&);
template bool sparse_matrix<double, double>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<double>&, lp_settings&);
template bool sparse_matrix<double, double>::shorten_active_matrix(unsigned int, eta_matrix<double, double>*);
template void sparse_matrix<double, double>::solve_y_U(vector<double>&) const;
template sparse_matrix<double, double>::sparse_matrix(static_matrix<double, double> const&, vector<unsigned int>&);
template sparse_matrix<double, double>::sparse_matrix(unsigned int);
template void     sparse_matrix<mpq, mpq>::add_new_element(unsigned int, unsigned int, const mpq&);
template void     sparse_matrix<mpq, mpq>::divide_row_by_constant(unsigned int, const mpq&, lp_settings&);
template bool sparse_matrix<mpq, mpq>::fill_eta_matrix(unsigned int, eta_matrix<mpq, mpq>**);
template  mpq const & sparse_matrix<mpq, mpq>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<mpq, mpq>::get_number_of_nonzeroes() const;
template bool sparse_matrix<mpq, mpq>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned sparse_matrix<mpq, mpq>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<mpq, mpq>::pivot_with_eta(unsigned int, eta_matrix<mpq, mpq>*, lp_settings&);
template void  sparse_matrix<mpq, mpq>::prepare_for_factorization();
template void   sparse_matrix<mpq, mpq>::remove_element(vector<indexed_value<mpq>> &, indexed_value<mpq>&);
template void     sparse_matrix<mpq, mpq>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     sparse_matrix<mpq, mpq>::set_max_in_row(vector<indexed_value<mpq>>&);
template bool sparse_matrix<mpq, mpq>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool sparse_matrix<mpq, mpq>::shorten_active_matrix(unsigned int, eta_matrix<mpq, mpq>*);
template void     sparse_matrix<mpq, mpq>::solve_y_U(vector<mpq>&) const;
template sparse_matrix<mpq, mpq>::sparse_matrix(static_matrix<mpq, mpq> const&, vector<unsigned int>&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::add_new_element(unsigned int, unsigned int, const mpq&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::divide_row_by_constant(unsigned int, const mpq&, lp_settings&);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::fill_eta_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >**);
template const mpq & sparse_matrix<mpq, numeric_pair<mpq>>::get(unsigned int, unsigned int) const;
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::get_number_of_nonzeroes() const;
template bool sparse_matrix<mpq, numeric_pair<mpq>>::get_pivot_for_column(unsigned int&, unsigned int&, int, unsigned int);
template unsigned sparse_matrix<mpq, numeric_pair<mpq>>::lowest_row_in_column(unsigned int);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::pivot_with_eta(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::prepare_for_factorization();
template void     sparse_matrix<mpq, numeric_pair<mpq>>::remove_element(vector<indexed_value<mpq>>&, indexed_value<mpq>&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::replace_column(unsigned int, indexed_vector<mpq>&, lp_settings&);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::set_max_in_row(vector<indexed_value<mpq>>&);
template bool sparse_matrix<mpq, numeric_pair<mpq>>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned int, indexed_vector<mpq>&, lp_settings&);
template bool     sparse_matrix<mpq, numeric_pair<mpq>>::shorten_active_matrix(unsigned int, eta_matrix<mpq, numeric_pair<mpq> >*);
template void     sparse_matrix<mpq, numeric_pair<mpq>>::solve_y_U(vector<mpq>&) const;
template sparse_matrix<mpq, numeric_pair<mpq>>::sparse_matrix(static_matrix<mpq, numeric_pair<mpq> > const&, vector<unsigned int>&);
template void sparse_matrix<double, double>::double_solve_U_y<double>(indexed_vector<double>&, const lp_settings  &);
template void sparse_matrix<mpq, mpq>::double_solve_U_y<mpq>(indexed_vector<mpq>&, const lp_settings&);
template void sparse_matrix<mpq, numeric_pair<mpq>>::double_solve_U_y<mpq>(indexed_vector<mpq>&, const lp_settings&);
template void sparse_matrix<mpq, numeric_pair<mpq> >::double_solve_U_y<numeric_pair<mpq> >(indexed_vector<numeric_pair<mpq>>&, const lp_settings&);
template void lp::sparse_matrix<double, double>::solve_U_y_indexed_only<double>(lp::indexed_vector<double>&, const lp_settings&, vector<unsigned> &);
template void lp::sparse_matrix<lp::mpq, lp::mpq>::solve_U_y_indexed_only<lp::mpq>(lp::indexed_vector<lp::mpq>&, const lp_settings &, vector<unsigned> &);
#ifdef Z3DEBUG
template bool sparse_matrix<double, double>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool sparse_matrix<mpq, mpq>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
template bool sparse_matrix<mpq, numeric_pair<mpq> >::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings&) const;
#endif
}
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_U_y_indexed_only<lp::mpq>(lp::indexed_vector<lp::mpq>&, const lp_settings &, vector<unsigned> &);
template void lp::sparse_matrix<lp::mpq, lp::mpq>::solve_U_y<lp::mpq>(vector<lp::mpq>&);
template void lp::sparse_matrix<lp::mpq, lp::mpq>::double_solve_U_y<lp::mpq>(vector<lp::mpq >&);
template void lp::sparse_matrix<double, double>::solve_U_y<double>(vector<double>&);
template void lp::sparse_matrix<double, double>::double_solve_U_y<double>(vector<double>&);
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_U_y<lp::numeric_pair<lp::mpq> >(vector<lp::numeric_pair<lp::mpq> >&);
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::double_solve_U_y<lp::numeric_pair<lp::mpq> >(vector<lp::numeric_pair<lp::mpq> >&);
template void lp::sparse_matrix<double, double>::find_error_in_solution_U_y_indexed<double>(lp::indexed_vector<double>&, lp::indexed_vector<double>&, const vector<unsigned> &);
template double lp::sparse_matrix<double, double>::dot_product_with_row<double>(unsigned int, lp::indexed_vector<double> const&) const;
template void lp::sparse_matrix<lp::mpq, lp::mpq>::find_error_in_solution_U_y_indexed<lp::mpq>(lp::indexed_vector<lp::mpq>&, lp::indexed_vector<lp::mpq>&, const vector<unsigned> &);
template lp::mpq lp::sparse_matrix<lp::mpq, lp::mpq>::dot_product_with_row<lp::mpq>(unsigned int, lp::indexed_vector<lp::mpq> const&) const;
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::find_error_in_solution_U_y_indexed<lp::mpq>(lp::indexed_vector<lp::mpq>&, lp::indexed_vector<lp::mpq>&, const vector<unsigned> &);
template lp::mpq lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::dot_product_with_row<lp::mpq>(unsigned int, lp::indexed_vector<lp::mpq> const&) const;
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::find_error_in_solution_U_y_indexed<lp::numeric_pair<lp::mpq> >(lp::indexed_vector<lp::numeric_pair<lp::mpq> >&, lp::indexed_vector<lp::numeric_pair<lp::mpq> >&, const vector<unsigned> &);
template lp::numeric_pair<lp::mpq> lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::dot_product_with_row<lp::numeric_pair<lp::mpq> >(unsigned int, lp::indexed_vector<lp::numeric_pair<lp::mpq> > const&) const;
template void lp::sparse_matrix<lp::mpq, lp::mpq>::extend_and_sort_active_rows(vector<unsigned int> const&, vector<unsigned int>&);

template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::extend_and_sort_active_rows(vector<unsigned int> const&, vector<unsigned int>&);

template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_U_y<lp::mpq>(vector<lp::mpq >&);
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::double_solve_U_y<lp::mpq>(vector<lp::mpq >&);
template void lp::sparse_matrix< lp::mpq,lp::numeric_pair< lp::mpq> >::set(unsigned int,unsigned int, lp::mpq);
template void lp::sparse_matrix<double, double>::solve_y_U_indexed(lp::indexed_vector<double>&, const lp_settings & );
template void lp::sparse_matrix<lp::mpq, lp::mpq>::solve_y_U_indexed(lp::indexed_vector<lp::mpq>&, const lp_settings &);
template void lp::sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::solve_y_U_indexed(lp::indexed_vector<lp::mpq>&, const lp_settings &);

