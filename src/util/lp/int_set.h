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
#include "util/lp/indexed_vector.h"
#include <ostream>
namespace lp {
// serves at a set of non-negative integers smaller than the set size
class int_set {
    vector<int> m_data;
public:
    vector<int> m_index;
    int_set(unsigned size): m_data(size, -1) {}
    int_set() {}
    bool contains(unsigned j) const {
        if (j >= m_data.size())
            return false;
        return m_data[j] >= 0;
    }
    void insert(unsigned j) {
        lp_assert(j < m_data.size());
        if (contains(j)) return;
        m_data[j] = m_index.size();
        m_index.push_back(j);
    }
    void erase(unsigned j) {
        if (!contains(j)) return;
        unsigned pos_j = m_data[j];
        unsigned last_pos = m_index.size() - 1;
        int last_j = m_index[last_pos];
        if (last_pos != pos_j) {
            // move last to j spot
            m_data[last_j] = pos_j;
            m_index[pos_j] = last_j;
        }
        m_index.pop_back();
        m_data[j] = -1;
    }

    void resize(unsigned size) {
        m_data.resize(size, -1);
    }

    void increase_size_by_one() {
        resize(m_data.size() + 1);
    }

    unsigned data_size() const {  return m_data.size(); }
    unsigned size() const { return m_index.size();}
    bool is_empty() const { return size() == 0; }
    void clear() {
        for (unsigned j : m_index)
            m_data[j] = -1;
        m_index.resize(0);
    }
    void print(std::ostream & out ) const {
        for (unsigned j : m_index) {
            out << j << " ";
        }
        out << std::endl;
    }
    
};
}
