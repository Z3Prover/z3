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
#include "util/lp/iterator_on_indexed_vector.h"
namespace lp {
template <typename T>
struct iterator_on_pivot_row:linear_combination_iterator<T> {
    bool m_basis_returned;
    const indexed_vector<T> & m_v;
    unsigned m_basis_j;
    iterator_on_indexed_vector<T> m_it;
    unsigned size() const override { return m_it.size(); }
    iterator_on_pivot_row(const indexed_vector<T> & v, unsigned basis_j) :
        m_basis_returned(false),
        m_v(v), m_basis_j(basis_j), m_it(v) {}
    bool next(T & a, unsigned & i) override {
        if (m_basis_returned == false) {
            m_basis_returned = true;
            a = one_of_type<T>();
            i = m_basis_j;
            return true;
        }
        return m_it.next(a, i);
    }
    bool next(unsigned & i) override {
        if (m_basis_returned == false) {
            m_basis_returned = true;
            i = m_basis_j;
            return true;
        }
        return m_it.next(i);
    }
    void reset() override {
        m_basis_returned = false;
        m_it.reset();
    }
    linear_combination_iterator<T> * clone() override {
        iterator_on_pivot_row * r = new iterator_on_pivot_row(m_v, m_basis_j);
        return r;
    }
};
}
