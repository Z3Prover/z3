/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <memory>
#include "util/vector.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/eta_matrix.hpp"
#ifdef LEAN_DEBUG
template double lean::eta_matrix<double, double>::get_elem(unsigned int, unsigned int) const;
template lean::mpq lean::eta_matrix<lean::mpq, lean::mpq>::get_elem(unsigned int, unsigned int) const;
template lean::mpq lean::eta_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::get_elem(unsigned int, unsigned int) const;
#endif
template void lean::eta_matrix<double, double>::apply_from_left(vector<double>&, lean::lp_settings&);
template void lean::eta_matrix<double, double>::apply_from_right(vector<double>&);
template void lean::eta_matrix<double, double>::conjugate_by_permutation(lean::permutation_matrix<double, double>&);
template void lean::eta_matrix<lean::mpq, lean::mpq>::apply_from_left(vector<lean::mpq>&, lean::lp_settings&);
template void lean::eta_matrix<lean::mpq, lean::mpq>::apply_from_right(vector<lean::mpq>&);
template void lean::eta_matrix<lean::mpq, lean::mpq>::conjugate_by_permutation(lean::permutation_matrix<lean::mpq, lean::mpq>&);
template void lean::eta_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_left(vector<lean::numeric_pair<lean::mpq> >&, lean::lp_settings&);
template void lean::eta_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_right(vector<lean::mpq>&);
template void lean::eta_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::conjugate_by_permutation(lean::permutation_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >&);
template void lean::eta_matrix<double, double>::apply_from_left_local<double>(lean::indexed_vector<double>&, lean::lp_settings&);
template void lean::eta_matrix<lean::mpq, lean::mpq>::apply_from_left_local<lean::mpq>(lean::indexed_vector<lean::mpq>&, lean::lp_settings&);
template void lean::eta_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_left_local<lean::mpq>(lean::indexed_vector<lean::mpq>&, lean::lp_settings&);
template void lean::eta_matrix<lean::mpq, lean::numeric_pair<lean::mpq> >::apply_from_right(lean::indexed_vector<lean::mpq>&);
template void lean::eta_matrix<lean::mpq, lean::mpq>::apply_from_right(lean::indexed_vector<lean::mpq>&);
template void lean::eta_matrix<double, double>::apply_from_right(lean::indexed_vector<double>&);
