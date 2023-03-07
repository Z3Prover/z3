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
#include "math/lp/permutation_matrix_def.h"
#include "math/lp/numeric_pair.h"
template void lp::permutation_matrix<lp::mpq, lp::mpq>::init(unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq>>::init(unsigned int);

template void lp::permutation_matrix<lp::mpq, lp::mpq>::apply_from_right(vector<lp::mpq>&);
template bool lp::permutation_matrix<lp::mpq, lp::mpq>::is_identity() const;
template void lp::permutation_matrix<lp::mpq, lp::mpq>::multiply_by_permutation_from_left(lp::permutation_matrix<lp::mpq, lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::multiply_by_permutation_from_right(lp::permutation_matrix<lp::mpq, lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::multiply_by_permutation_reverse_from_left(lp::permutation_matrix<lp::mpq, lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::multiply_by_reverse_from_right(lp::permutation_matrix<lp::mpq, lp::mpq>&);
template lp::permutation_matrix<lp::mpq, lp::mpq>::permutation_matrix(unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::transpose_from_left(unsigned int, unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::transpose_from_right(unsigned int, unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_right(vector<lp::mpq>&);
template bool lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::is_identity() const;
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::multiply_by_permutation_from_left(lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::multiply_by_permutation_from_right(lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::multiply_by_permutation_reverse_from_left(lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::multiply_by_reverse_from_right(lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::permutation_matrix(unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::transpose_from_left(unsigned int, unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::transpose_from_right(unsigned int, unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::apply_reverse_from_left<lp::mpq>(lp::indexed_vector<lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::apply_reverse_from_left_to_T(vector<lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::apply_reverse_from_right_to_T(vector<lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_reverse_from_left<lp::mpq>(lp::indexed_vector<lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_reverse_from_left_to_T(vector<lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_reverse_from_right_to_T(vector<lp::mpq >&);
template void  lp::permutation_matrix< lp::mpq, lp::mpq>::apply_reverse_from_left_to_X(vector<lp::mpq> &);
template void lp::permutation_matrix< lp::mpq, lp::numeric_pair< lp::mpq> >::apply_reverse_from_left_to_X(vector<lp::numeric_pair< lp::mpq>> &);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::apply_reverse_from_right_to_T(lp::indexed_vector<lp::mpq>&);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_reverse_from_right_to_T(lp::indexed_vector<lp::mpq>&);
