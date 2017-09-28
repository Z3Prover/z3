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
#ifdef Z3DEBUG
#include "util/lp/matrix.hpp"
#include "util/lp/static_matrix.h"
#include <string>
template void lp::print_matrix<double, double>(lp::matrix<double, double> const*, std::ostream & out);
template bool lp::matrix<double, double>::is_equal(lp::matrix<double, double> const&);
template void lp::print_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >(lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> > const *, std::basic_ostream<char, std::char_traits<char> > &);
template void lp::print_matrix<lp::mpq, lp::mpq>(lp::matrix<lp::mpq, lp::mpq> const*, std::ostream&);
template bool lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::is_equal(lp::matrix<lp::mpq, lp::numeric_pair<lp::mpq> > const&);
template bool lp::matrix<lp::mpq, lp::mpq>::is_equal(lp::matrix<lp::mpq, lp::mpq> const&);
#endif
