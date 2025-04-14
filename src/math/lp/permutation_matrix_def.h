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
#pragma once

#include "util/vector.h"
#include "math/lp/permutation_matrix.h"
namespace lp {
template <typename T, typename X> permutation_matrix<T, X>::permutation_matrix(unsigned length): m_permutation(length), m_rev(length)  {
    for (unsigned i = 0; i < length; i++) { // do not change the direction of the loop because of the vectorization bug in clang3.3
        m_permutation[i] = m_rev[i] = i;
    }
}

template <typename T, typename X> permutation_matrix<T, X>::permutation_matrix(unsigned length, vector<unsigned> const & values): m_permutation(length), m_rev(length) {
    for (unsigned i = 0; i < length; i++) {
        set_val(i, values[i]);
    }
}
// create a unit permutation of the given length
template <typename T, typename X> void permutation_matrix<T, X>::init(unsigned length) {
    m_permutation.resize(length);
    m_rev.resize(length);
    for (unsigned i = 0; i < length; i++) {
        m_permutation[i] = m_rev[i] = i;
    }
}

#ifdef Z3DEBUG
template <typename T, typename X> void permutation_matrix<T, X>::print(std::ostream & out) const {
    out << "[";
    for (unsigned i = 0; i < size(); i++) {
        out << m_permutation[i];
        if (i < size() - 1) {
            out << ",";
        } else {
            out << "]";
        }
    }
    out << std::endl;
}
#endif


template <typename T, typename X> void permutation_matrix<T, X>::transpose_from_left(unsigned i, unsigned j) {
    // the result will be this = (i,j)*this
    SASSERT(i < size() && j < size() && i != j);
    auto pi = m_rev[i];
    auto pj = m_rev[j];
    set_val(pi, j);
    set_val(pj, i);
}

template <typename T, typename X> void permutation_matrix<T, X>::transpose_from_right(unsigned i, unsigned j) {
    // the result will be this = this * (i,j)
    SASSERT(i < size() && j < size() && i != j);
    auto pi = m_permutation[i];
    auto pj = m_permutation[j];
    set_val(i, pj);
    set_val(j, pi);
}


}
