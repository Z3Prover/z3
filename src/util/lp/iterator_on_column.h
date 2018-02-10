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
#include "util/lp/linear_combination_iterator.h"
#include "util/lp/static_matrix.h"
#include "util/lp/lar_term.h"
namespace lp {
template <typename T, typename X>
struct iterator_on_column:linear_combination_iterator<T> {
    const vector<column_cell>& m_column; // the offset in term coeffs
    const static_matrix<T, X> & m_A;
    int m_i; // the initial offset in the column
    unsigned size() const override { return m_column.size(); }
    iterator_on_column(const vector<column_cell>& column, const static_matrix<T,X> & A) // the offset in term coeffs
        :
        m_column(column),
        m_A(A),
        m_i(-1) {}
    
    bool next(mpq & a, unsigned & i) override {
        if (++m_i >= static_cast<int>(m_column.size()))
            return false;

        const column_cell& c = m_column[m_i];
        a = m_A.get_val(c);
        i = c.m_i;
        return true;
    }

    bool next(unsigned & i) override {
        if (++m_i >= static_cast<int>(m_column.size()))
            return false;

        const column_cell& c = m_column[m_i];
        i = c.m_i;
        return true;
    }
    
    void reset() override {
        m_i = -1;
    }

    linear_combination_iterator<mpq> * clone() override {
        iterator_on_column * r = new iterator_on_column(m_column, m_A);
        return r;
    }
};
}
