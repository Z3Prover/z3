/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/lp/linear_combination_iterator.h"
namespace lp {
template <typename T>
struct linear_combination_iterator_on_std_vector_with_additional_element : linear_combination_iterator<T> {
    std::vector<std::pair<T, unsigned>> & m_vector;
    int m_offset;
    unsigned m_additional_element;
    bool m_additional_element_is_returned;
    bool next(T & a, unsigned & i) {
        if (m_additional_element_is_returned == false) {
            m_additional_element_is_returned = true;
            i = m_additional_element;
            a = one_of_type<T>();
            return true;
        }
        if(m_offset >= static_cast<int>(m_vector.size()))
            return false;
        auto & p = m_vector[m_offset];
        a = p.first;
        i = p.second;
        m_offset++;
        return true;
    }

    bool next(unsigned & i) {
        if (m_additional_element_is_returned == false) {
            m_additional_element_is_returned = true;
            i = m_additional_element;
            return true;
        }
        if(m_offset >= static_cast<int>(m_vector.size()))
            return false;
        auto & p = m_vector[m_offset];
        i = p.second;
        m_offset++;
        return true;
    }
    bool is_reset() const { return m_offset == 0 && m_additional_element_is_returned == false;}
    void reset() {
        m_additional_element_is_returned = false;
        m_offset = 0;
    }
    linear_combination_iterator<T> * clone() {
        return new linear_combination_iterator_on_std_vector_with_additional_element(m_vector, m_additional_element);
    }
    linear_combination_iterator_on_std_vector_with_additional_element(std::vector<std::pair<T, unsigned>> & vec, unsigned additional_element):
        m_vector(vec),
        m_offset(0),
        m_additional_element(additional_element),
        m_additional_element_is_returned(false)
    {}
    unsigned size() const { return m_vector.size(); }
};

}
