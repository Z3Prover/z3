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
template void indexed_vector<mpq>::clear();
template void indexed_vector<unsigned>::clear();
template void indexed_vector<mpq>::clear_all();
template void indexed_vector<mpq>::erase_from_index(unsigned int);
template void indexed_vector<mpq>::resize(unsigned int);
template void indexed_vector<unsigned>::resize(unsigned int);
template void indexed_vector<mpq>::set_value(const mpq&, unsigned int);
template void indexed_vector<unsigned>::set_value(const unsigned&, unsigned int);
template void indexed_vector<mpq>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void indexed_vector<numeric_pair<lp::mpq> >::print(std::ostream&);
template void indexed_vector<mpq>::erase(unsigned int);
}
template void lp::indexed_vector<lp::numeric_pair<lp::mpq> >::erase_from_index(unsigned int);


