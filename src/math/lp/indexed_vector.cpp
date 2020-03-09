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
#include "util/vector.h"
#include "math/lp/indexed_vector_def.h"
namespace lp {
template void indexed_vector<double>::clear();
template void indexed_vector<double>::clear_all();
template void indexed_vector<double>::erase_from_index(unsigned int);
template void indexed_vector<double>::set_value(const double&, unsigned int);
template void indexed_vector<mpq>::clear();
template void indexed_vector<unsigned>::clear();
template void indexed_vector<mpq>::clear_all();
template void indexed_vector<mpq>::erase_from_index(unsigned int);
template void indexed_vector<mpq>::resize(unsigned int);
template void indexed_vector<unsigned>::resize(unsigned int);
template void indexed_vector<mpq>::set_value(const mpq&, unsigned int);
template void indexed_vector<unsigned>::set_value(const unsigned&, unsigned int);
#ifdef Z3DEBUG
template bool indexed_vector<unsigned>::is_OK() const;
template bool indexed_vector<double>::is_OK() const;
template bool indexed_vector<mpq>::is_OK() const;
template bool indexed_vector<lp::numeric_pair<mpq> >::is_OK() const;
#endif
template void lp::indexed_vector< lp::mpq>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void lp::indexed_vector<double>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void lp::indexed_vector<lp::numeric_pair<lp::mpq> >::print(std::ostream&);
}
// template void lp::print_vector<double, vectro>(vector<double> const&, std::ostream&);
// template void lp::print_vector<unsigned int>(vector<unsigned int> const&, std::ostream&);
// template void lp::print_vector<std::string>(vector<std::string> const&, std::ostream&);
// template void lp::print_vector<lp::numeric_pair<lp::mpq> >(vector<lp::numeric_pair<lp::mpq>> const&, std::ostream&);
template void lp::indexed_vector<double>::resize(unsigned int);
// template void lp::print_vector< lp::mpq>(vector< lp::mpq> const &, std::basic_ostream<char, std::char_traits<char> > &);
// template void lp::print_vector<std::pair<lp::mpq, unsigned int> >(vector<std::pair<lp::mpq, unsigned int>> const&, std::ostream&);
template void lp::indexed_vector<lp::numeric_pair<lp::mpq> >::erase_from_index(unsigned int);

