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
#include "math/lp/numeric_pair.h"
#include "math/lp/eta_matrix_def.h"
#ifdef Z3DEBUG
template double lp::eta_matrix<double, double>::get_elem(unsigned int, unsigned int) const;
template lp::mpq lp::eta_matrix<lp::mpq, lp::mpq>::get_elem(unsigned int, unsigned int) const;
template lp::mpq lp::eta_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::get_elem(unsigned int, unsigned int) const;
#endif
template void lp::eta_matrix<double, double>::apply_from_left(vector<double>&, lp::lp_settings&);
template void lp::eta_matrix<double, double>::apply_from_right(vector<double>&);
template void lp::eta_matrix<double, double>::conjugate_by_permutation(lp::permutation_matrix<double, double>&);
template void lp::eta_matrix<lp::mpq, lp::mpq>::apply_from_left(vector<lp::mpq>&, lp::lp_settings&);
template void lp::eta_matrix<lp::mpq, lp::mpq>::apply_from_right(vector<lp::mpq>&);
template void lp::eta_matrix<lp::mpq, lp::mpq>::conjugate_by_permutation(lp::permutation_matrix<lp::mpq, lp::mpq>&);
template void lp::eta_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_left(vector<lp::numeric_pair<lp::mpq> >&, lp::lp_settings&);
template void lp::eta_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_right(vector<lp::mpq>&);
template void lp::eta_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::conjugate_by_permutation(lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template void lp::eta_matrix<double, double>::apply_from_left_local<double>(lp::indexed_vector<double>&, lp::lp_settings&);
template void lp::eta_matrix<lp::mpq, lp::mpq>::apply_from_left_local<lp::mpq>(lp::indexed_vector<lp::mpq>&, lp::lp_settings&);
template void lp::eta_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_left_local<lp::mpq>(lp::indexed_vector<lp::mpq>&, lp::lp_settings&);
template void lp::eta_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_right(lp::indexed_vector<lp::mpq>&);
template void lp::eta_matrix<lp::mpq, lp::mpq>::apply_from_right(lp::indexed_vector<lp::mpq>&);
template void lp::eta_matrix<double, double>::apply_from_right(lp::indexed_vector<double>&);
