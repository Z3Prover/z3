/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/vector.h"
#include "util/lp/indexed_vector.hpp"
namespace lean {
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
#ifdef LEAN_DEBUG
template bool indexed_vector<double>::is_OK() const;
template bool indexed_vector<mpq>::is_OK() const;
template bool indexed_vector<lean::numeric_pair<mpq> >::is_OK() const;
template void lean::indexed_vector< lean::mpq>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void lean::indexed_vector<double>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void lean::indexed_vector<lean::numeric_pair<lean::mpq> >::print(std::ostream&);
#endif
}
template void lean::print_vector<double>(vector<double> const&, std::ostream&);
template void lean::print_vector<unsigned int>(vector<unsigned int> const&, std::ostream&);
template void lean::print_vector<std::string>(vector<std::string> const&, std::ostream&);
template void lean::print_vector<lean::numeric_pair<lean::mpq> >(vector<lean::numeric_pair<lean::mpq>> const&, std::ostream&);
template void lean::indexed_vector<double>::resize(unsigned int);
template void lean::print_vector< lean::mpq>(vector< lean::mpq> const &, std::basic_ostream<char, std::char_traits<char> > &);
template void lean::print_vector<std::pair<lean::mpq, unsigned int> >(vector<std::pair<lean::mpq, unsigned int>> const&, std::ostream&);
template void lean::indexed_vector<lean::numeric_pair<lean::mpq> >::erase_from_index(unsigned int);
