/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <memory>
#include "util/vector.h"
#include "util/lp/permutation_matrix.hpp"
#include "util/lp/numeric_pair.h"
template void lean::permutation_matrix<double, double>::apply_from_right(vector<double>&);
template void lean::permutation_matrix<double, double>::init(unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::init(unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq>>::init(unsigned int);
template bool lean::permutation_matrix<double, double>::is_identity() const;
template void lean::permutation_matrix<double, double>::multiply_by_permutation_from_left(lean::permutation_matrix<double, double>&);
template void lean::permutation_matrix<double, double>::multiply_by_permutation_reverse_from_left(lean::permutation_matrix<double, double>&);
template void lean::permutation_matrix<double, double>::multiply_by_reverse_from_right(lean::permutation_matrix<double, double>&);
template lean::permutation_matrix<double, double>::permutation_matrix(unsigned int, vector<unsigned int> const&);
template void lean::permutation_matrix<double, double>::transpose_from_left(unsigned int, unsigned int);

template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_from_right(vector<lean::mpq>&);
template bool lean::permutation_matrix<lean::mpq, lean::mpq>::is_identity() const;
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_permutation_from_left(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_permutation_from_right(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_permutation_reverse_from_left(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::multiply_by_reverse_from_right(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template lean::permutation_matrix<lean::mpq, lean::mpq>::permutation_matrix(unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::transpose_from_left(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_right(vector<lean::mpq>&);
template bool lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::is_identity() const;
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_permutation_from_left(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_permutation_from_right(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_permutation_reverse_from_left(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::multiply_by_reverse_from_right(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::permutation_matrix(unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::transpose_from_left(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<double, double>::apply_reverse_from_left<double>(lean::indexed_vector<double>&);
template void lean::permutation_matrix<double, double>::apply_reverse_from_left_to_T(vector<double>&);
template void lean::permutation_matrix<double, double>::apply_reverse_from_right_to_T(vector<double>&);
template void lean::permutation_matrix<double, double>::transpose_from_right(unsigned int, unsigned int);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_left<lean::mpq>(lean::indexed_vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_left_to_T(vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_right_to_T(vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_left<lean::mpq>(lean::indexed_vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_left_to_T(vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_right_to_T(vector<lean::mpq >&);
template void lean::permutation_matrix<double, double>::multiply_by_permutation_from_right(lean::permutation_matrix<double, double>&);
template lean::permutation_matrix<double, double>::permutation_matrix(unsigned int);
template void lean::permutation_matrix<double, double>::apply_reverse_from_left_to_X(vector<double> &);
template void  lean::permutation_matrix< lean::mpq, lean::mpq>::apply_reverse_from_left_to_X(vector<lean::mpq> &);
template void lean::permutation_matrix< lean::mpq, lean::numeric_pair< lean::mpq> >::apply_reverse_from_left_to_X(vector<lean::numeric_pair< lean::mpq>> &);
template void lean::permutation_matrix<double, double>::apply_reverse_from_right_to_T(lean::indexed_vector<double>&);
template void lean::permutation_matrix<lean::mpq, lean::mpq>::apply_reverse_from_right_to_T(lean::indexed_vector<lean::mpq>&);
template void lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_reverse_from_right_to_T(lean::indexed_vector<lean::mpq>&);
