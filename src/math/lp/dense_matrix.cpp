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
// clang-format off
#include "math/lp/lp_settings.h"
#include "math/lp/dense_matrix_def.h"
#ifdef Z3DEBUG
#include "util/vector.h"
template lp::dense_matrix<lp::mpq, lp::mpq>::dense_matrix(unsigned int, unsigned int);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::dense_matrix(lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> > const*);
template void lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_left(vector<lp::mpq>&);
template lp::dense_matrix<lp::mpq, lp::mpq> lp::operator*<lp::mpq, lp::mpq>(lp::matrix<lp::mpq, lp::mpq>&, lp::matrix<lp::mpq, lp::mpq>&);
template lp::dense_matrix<lp::mpq, lp::mpq> & lp::dense_matrix<lp::mpq, lp::mpq>::operator=(lp::dense_matrix<lp::mpq, lp::mpq> const&);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::dense_matrix(unsigned int, unsigned int);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >& lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::operator=(lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> > const&);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> > lp::operator*<lp::mpq, lp::numeric_pair<lp::mpq> >(lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&, lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template void lp::dense_matrix<lp::mpq, lp::numeric_pair< lp::mpq> >::apply_from_right( vector< lp::mpq> &);
template void lp::dense_matrix<lp::mpq, lp::mpq>::apply_from_left(vector<lp::mpq>&);
#endif
