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
#include "math/lp/lu_def.h"
namespace lp {
template double dot_product<double, double>(vector<double> const&, vector<double> const&);
template lu<static_matrix<double, double>>::lu(static_matrix<double, double> const&, vector<unsigned int>&, lp_settings&);
template void lu<static_matrix<double, double>>::push_matrix_to_tail(tail_matrix<double, double>*);
template void lu<static_matrix<double, double>>::replace_column(double, indexed_vector<double>&, unsigned);
template void lu<static_matrix<double, double>>::solve_Bd(unsigned int, indexed_vector<double>&, indexed_vector<double>&);
template lu<static_matrix<double, double>>::~lu();
template void lu<static_matrix<mpq, mpq>>::push_matrix_to_tail(tail_matrix<mpq, mpq>*);
template void lu<static_matrix<mpq, mpq>>::solve_Bd(unsigned int, indexed_vector<mpq>&, indexed_vector<mpq>&);
template lu<static_matrix<mpq, mpq>>::~lu();
template void lu<static_matrix<mpq, impq>>::push_matrix_to_tail(tail_matrix<mpq, impq >*);
template void lu<static_matrix<mpq, impq>>::solve_Bd(unsigned int, indexed_vector<mpq>&, indexed_vector<mpq>&);
template lu<static_matrix<mpq, impq>>::~lu();
template mpq dot_product<mpq, mpq>(vector<mpq > const&, vector<mpq > const&);
template void init_factorization<static_matrix<double, double>>
    (lu<static_matrix<double, double>>*&, static_matrix<double, double>&, vector<unsigned int>&, lp_settings&);
template void init_factorization<static_matrix<mpq, mpq>>
    (lu<static_matrix<mpq,mpq>>*&, static_matrix<mpq, mpq>&, vector<unsigned int>&, lp_settings&);
template void init_factorization<static_matrix<mpq, impq>>(lu<static_matrix<mpq, impq> >*&, static_matrix<mpq, impq >&, vector<unsigned int>&, lp_settings&);
template void print_matrix<square_sparse_matrix<double, double>>(square_sparse_matrix<double, double>&, std::ostream & out);
template void print_matrix<static_matrix<mpq,mpq>>(static_matrix<mpq, mpq>&, std::ostream&);
template void print_matrix<static_matrix<mpq, impq> >(static_matrix<mpq, impq >&, std::ostream&);
template void print_matrix<static_matrix<double, double>>(static_matrix<double, double>&, std::ostream & out);
#ifdef Z3DEBUG
template bool lu<static_matrix<double, double>>::is_correct(const vector<unsigned>& basis);
template bool lu<static_matrix<mpq, impq>>::is_correct( vector<unsigned int> const &);
template dense_matrix<double, double> get_B<static_matrix<double, double>>(lu<static_matrix<double, double>>&, const vector<unsigned>& basis);
template dense_matrix<mpq, mpq> get_B<static_matrix<mpq, mpq>>(lu<static_matrix<mpq, mpq>>&, vector<unsigned int> const&);

#endif

template bool lu<static_matrix<double, double>>::pivot_the_row(int); // NOLINT
template void lu<static_matrix<double, double>>::init_vector_w(unsigned int, indexed_vector<double>&);
template void lu<static_matrix<double, double>>::solve_By(vector<double>&);
template void lu<static_matrix<double, double>>::solve_By_when_y_is_ready_for_X(vector<double>&);
template void lu<static_matrix<double, double>>::solve_yB_with_error_check(vector<double>&, const vector<unsigned>& basis);
template void lu<static_matrix<double, double>>::solve_yB_with_error_check_indexed(indexed_vector<double>&, vector<int> const&,  const vector<unsigned> & basis, const lp_settings&);
template void lu<static_matrix<mpq, mpq>>::replace_column(mpq, indexed_vector<mpq>&, unsigned);
template void lu<static_matrix<mpq, mpq>>::solve_By(vector<mpq >&);
template void lu<static_matrix<mpq, mpq>>::solve_By_when_y_is_ready_for_X(vector<mpq >&);
template void lu<static_matrix<mpq, mpq>>::solve_yB_with_error_check(vector<mpq >&, const vector<unsigned>& basis);
template void lu<static_matrix<mpq, mpq>>::solve_yB_with_error_check_indexed(indexed_vector<mpq>&, vector< int > const&,  const vector<unsigned> & basis, const lp_settings&);
template void lu<static_matrix<mpq, impq> >::solve_yB_with_error_check_indexed(indexed_vector<mpq>&, vector< int > const&,  const vector<unsigned> & basis, const lp_settings&);
template void lu<static_matrix<mpq, impq> >::init_vector_w(unsigned int, indexed_vector<mpq>&);
template void lu<static_matrix<mpq, impq> >::replace_column(mpq, indexed_vector<mpq>&, unsigned);
template void lu<static_matrix<mpq, impq> >::solve_Bd_faster(unsigned int, indexed_vector<mpq>&);
template void lu<static_matrix<mpq, impq> >::solve_By(vector<impq >&);
template void lu<static_matrix<mpq, impq> >::solve_By_when_y_is_ready_for_X(vector<impq >&);
template void lu<static_matrix<mpq, impq> >::solve_yB_with_error_check(vector<mpq >&, const vector<unsigned>& basis);
template void lu<static_matrix<mpq, mpq>>::solve_By(indexed_vector<mpq>&);
template void lu<static_matrix<double, double>>::solve_By(indexed_vector<double>&);
template void lu<static_matrix<double, double>>::solve_yB_indexed(indexed_vector<double>&);
template void lu<static_matrix<mpq, impq> >::solve_yB_indexed(indexed_vector<mpq>&);
template void lu<static_matrix<mpq, mpq>>::solve_By_for_T_indexed_only(indexed_vector<mpq>&, lp_settings const&);
template void lu<static_matrix<double, double>>::solve_By_for_T_indexed_only(indexed_vector<double>&, lp_settings const&);
#ifdef Z3DEBUG
template void print_matrix<tail_matrix<double, double>>(tail_matrix<double, double>&, std::ostream&);
#endif
}
