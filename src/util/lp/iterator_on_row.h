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
namespace lp {
template <typename T>
struct iterator_on_row:linear_combination_iterator<T> {
    const vector<row_cell<T>> & m_row;
    unsigned m_i; // offset
    iterator_on_row(const vector<row_cell<T>> & row) : m_row(row), m_i(0)
    {}
    unsigned size() const override { return m_row.size(); }
    bool next(T & a, unsigned & i) override {
        if (m_i == m_row.size())
            return false;
        auto &c = m_row[m_i++];
        i = c.m_j;
        a = c.get_val();
        return true;
    }
    bool next(unsigned & i) override {
        if (m_i == m_row.size())
            return false;
        auto &c = m_row[m_i++];
        i = c.m_j;
        return true;
    }
    void reset() override {
        m_i = 0;
    }
    linear_combination_iterator<T>* clone() override {
        return new iterator_on_row(m_row);
    }
};
}
