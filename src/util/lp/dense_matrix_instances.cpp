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
#include "util/lp/lp_settings.h"
#include "util/lp/dense_matrix.hpp"
#ifdef Z3DEBUG
#include "util/vector.h"
template lp::dense_matrix<double, double> lp::operator*<double, double>(lp::matrix<double, double>&, lp::matrix<double, double>&);
template void lp::dense_matrix<double, double>::apply_from_left(vector<double> &);
template lp::dense_matrix<double, double>::dense_matrix(lp::matrix<double, double> const*);
template lp::dense_matrix<double, double>::dense_matrix(unsigned int, unsigned int);
template lp::dense_matrix<double, double>& lp::dense_matrix<double, double>::operator=(lp::dense_matrix<double, double> const&);
template lp::dense_matrix<lp::mpq, lp::mpq>::dense_matrix(unsigned int, unsigned int);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::dense_matrix(lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> > const*);
template void lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::apply_from_left(vector<lp::mpq>&);
template lp::dense_matrix<lp::mpq, lp::mpq> lp::operator*<lp::mpq, lp::mpq>(lp::matrix<lp::mpq, lp::mpq>&, lp::matrix<lp::mpq, lp::mpq>&);
template lp::dense_matrix<lp::mpq, lp::mpq> & lp::dense_matrix<lp::mpq, lp::mpq>::operator=(lp::dense_matrix<lp::mpq, lp::mpq> const&);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::dense_matrix(unsigned int, unsigned int);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >& lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::operator=(lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> > const&);
template lp::dense_matrix<lp::mpq, lp::numeric_pair<lp::mpq> > lp::operator*<lp::mpq, lp::numeric_pair<lp::mpq> >(lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&, lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> >&);
template void lp::dense_matrix<lp::mpq, lp::numeric_pair< lp::mpq> >::apply_from_right( vector< lp::mpq> &);
template void lp::dense_matrix<double,double>::apply_from_right(class vector<double> &);
template void lp::dense_matrix<lp::mpq, lp::mpq>::apply_from_left(vector<lp::mpq>&);
#endif
