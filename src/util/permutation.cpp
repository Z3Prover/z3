/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    permutation.cpp

Abstract:

    Goodies for managing permutations.

Author:

    Leonardo de Moura (leonardo) 2011-06-10.

Revision History:

--*/
#include "util/permutation.h"

permutation::permutation(unsigned size) {
    reset(size);
}

void permutation::reset(unsigned size) {
    m_p.reset();
    m_inv_p.reset();
    for (unsigned i = 0; i < size; i++) {
        m_p.push_back(i);
        m_inv_p.push_back(i);
    }
}

void permutation::swap(unsigned i, unsigned j) {
    unsigned i_prime = m_p[i];
    unsigned j_prime = m_p[j];
    std::swap(m_p[i], m_p[j]);
    std::swap(m_inv_p[i_prime], m_inv_p[j_prime]); 
}

/**
   \brief Move i after j.
*/
void permutation::move_after(unsigned i, unsigned j) {
    if (i >= j)
        return;
    unsigned i_prime = m_p[i];
    for (unsigned k = i; k < j; k++) {
        m_p[k] = m_p[k+1];
        m_inv_p[m_p[k]] = k;
    }
    m_p[j] = i_prime;
    m_inv_p[i_prime] = j;
    SASSERT(check_invariant());
}

void permutation::display(std::ostream & out) const {
    unsigned n = m_p.size();
    for (unsigned i = 0; i < n; i++) {
        if (i > 0)
            out << " ";
        out << i << ":" << m_p[i];
    }
}

bool permutation::check_invariant() const {
    SASSERT(m_p.size() == m_inv_p.size());
    unsigned n = m_p.size();
    for (unsigned i = 0; i < n; i++) {
        SASSERT(m_p[i] < n);
        SASSERT(m_inv_p[i] < n);
        SASSERT(m_p[m_inv_p[i]] == i);
        SASSERT(m_inv_p[m_p[i]] == i);
    }
    return true;
}
