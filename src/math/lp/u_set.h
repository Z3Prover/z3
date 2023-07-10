/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:

TBD use indexed_uint_set from src/util/uint_set.h, 

--*/
#pragma once
#include "util/vector.h"
#include <ostream>
namespace lp {
// serves at a set of non-negative integers smaller than the set size
class u_set {
    svector<int> m_data;
    unsigned_vector m_index;

public:
    u_set(unsigned size): m_data(size, -1) {}
    u_set() {}
    u_set(u_set const& other):
        m_data(other.m_data),
        m_index(other.m_index) {}

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

    int operator[](unsigned j) const { return m_index[j]; }
    
    void resize(unsigned size) {
        if (size < data_size()) {
            bool copy = false;
            unsigned i = 0;
            for (unsigned j : m_index) {
                if (j < size) {
                    if (copy) {
                        m_data[j] = i;
                        m_index[i] = j;
                    }
                    i++;
                } else {
                    copy = true;
                }
            }
            m_index.shrink(i);
        }
        m_data.resize(size, -1);
    }

    void increase_size_by_one() {
        resize(m_data.size() + 1);
    }
   
    unsigned data_size() const {  return m_data.size(); }
    unsigned size() const { return m_index.size();}
    bool empty() const { return size() == 0; }
    void clear() {
        for (unsigned j : m_index)
            m_data[j] = -1;
        m_index.resize(0);
    }

    std::ostream& display(std::ostream& out) const {
        for (unsigned j : m_index) {
            out << j << " ";
        }
        out << std::endl;
        return out;
    }
    const unsigned * begin() const { return m_index.begin(); }
    const unsigned * end() const { return m_index.end(); }
    const unsigned_vector& index() { return m_index; }
};


}

inline std::ostream& operator<<(std::ostream& out, lp::u_set const& s) {
    return s.display(out);
}
