/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/lp/linear_combination_iterator.h"
namespace lp {
template <typename T>
struct linear_combination_iterator_on_std_vector : linear_combination_iterator<T> {
    std::vector<std::pair<T, unsigned>> & m_vector;
    int m_offset;
    bool next(T & a, unsigned & i) {
        if(m_offset >= static_cast<int>(m_vector.size()))
            return false;
        auto & p = m_vector[m_offset];
        a = p.first;
        i = p.second;
        m_offset++;
        return true;
    }

    bool next(unsigned & i) {
        if(m_offset >= static_cast<int>(m_vector.size()))
            return false;
        auto & p = m_vector[m_offset];
        i = p.second;
        m_offset++;
        return true;
    }
    bool is_reset() const { return m_offset == 0; }
    void reset() {
        m_offset = 0;
    }
    linear_combination_iterator<T> * clone() {
        return new linear_combination_iterator_on_std_vector(m_vector);
    }
    linear_combination_iterator_on_std_vector(std::vector<std::pair<T, unsigned>> & vec):
        m_vector(vec),
        m_offset(0) {}
    unsigned size() const { return m_vector.size(); }
};
}
