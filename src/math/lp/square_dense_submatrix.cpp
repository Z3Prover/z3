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
#include "math/lp/square_dense_submatrix_def.h"
template void lp::square_dense_submatrix<double, double>::init(lp::square_sparse_matrix<double, double>*, unsigned int);
template lp::square_dense_submatrix<double, double>::square_dense_submatrix(lp::square_sparse_matrix<double, double>*, unsigned int);
template void lp::square_dense_submatrix<double, double>::update_parent_matrix(lp::lp_settings&);
template bool lp::square_dense_submatrix<double, double>::is_L_matrix() const;
template void lp::square_dense_submatrix<double, double>::conjugate_by_permutation(lp::permutation_matrix<double, double>&);
template int lp::square_dense_submatrix<double, double>::find_pivot_column_in_row(unsigned int) const;
template void lp::square_dense_submatrix<double, double>::pivot(unsigned int, lp::lp_settings&);
template lp::square_dense_submatrix<lp::mpq, lp::numeric_pair<lp::mpq> >::square_dense_submatrix(lp::square_sparse_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >*, unsigned int);
template void lp::square_dense_submatrix<lp::mpq, lp::numeric_pair<lp::mpq> >::update_parent_matrix(lp::lp_settings&);
template bool lp::square_dense_submatrix<lp::mpq, lp::numeric_pair<lp::mpq> >::is_L_matrix() const;
template void lp::square_dense_submatrix<lp::mpq, lp::numeric_pair<lp::mpq> >::conjugate_by_permutation(lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template int lp::square_dense_submatrix<lp::mpq, lp::numeric_pair<lp::mpq> >::find_pivot_column_in_row(unsigned int) const;
template void lp::square_dense_submatrix<lp::mpq, lp::numeric_pair<lp::mpq> >::pivot(unsigned int, lp::lp_settings&);
#ifdef Z3DEBUG
template double lp::square_dense_submatrix<double, double>::get_elem(unsigned int, unsigned int) const;
#endif
template void lp::square_dense_submatrix<double, double>::apply_from_right(vector<double>&);
   
template void  lp::square_dense_submatrix<double, double>::apply_from_left_local<double>(lp::indexed_vector<double>&, lp::lp_settings&);
template void  lp::square_dense_submatrix<double, double>::apply_from_left_to_vector<double>(vector<double>&);
template lp::square_dense_submatrix<lp::mpq, lp::mpq>::square_dense_submatrix(lp::square_sparse_matrix<lp::mpq, lp::mpq>*, unsigned int);
template void lp::square_dense_submatrix<lp::mpq, lp::mpq>::update_parent_matrix(lp::lp_settings&);
template bool lp::square_dense_submatrix<lp::mpq, lp::mpq>::is_L_matrix() const;
template void lp::square_dense_submatrix<lp::mpq, lp::mpq>::conjugate_by_permutation(lp::permutation_matrix<lp::mpq, lp::mpq>&);
template int lp::square_dense_submatrix<lp::mpq, lp::mpq>::find_pivot_column_in_row(unsigned int) const;
template void lp::square_dense_submatrix<lp::mpq, lp::mpq>::pivot(unsigned int, lp::lp_settings&);
