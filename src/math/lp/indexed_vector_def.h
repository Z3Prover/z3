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
#include "math/lp/indexed_vector.h"
#include "math/lp/lp_settings.h"
namespace lp {


void print_vector_as_doubles(const vector<mpq> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++)
        out << t[i].get_double() << std::setprecision(3) << " ";
    out << std::endl;
}

template <typename T>
void indexed_vector<T>::resize(unsigned data_size) {
    m_data.resize(data_size, numeric_traits<T>::zero());
}

template <typename T>
void indexed_vector<T>::set_value(const T& value, unsigned index) {
    m_data[index] = value;
    SASSERT(std::find(m_index.begin(), m_index.end(), index) == m_index.end());
    m_index.push_back(index);
}

template <typename T>
void indexed_vector<T>::clear() {
    for (unsigned i : m_index)
        m_data[i] = numeric_traits<T>::zero();
    m_index.resize(0);
}
template <typename T>
void indexed_vector<T>::clear_all() {
    unsigned i = static_cast<unsigned>(m_data.size());
    while (i--)  m_data[i] = numeric_traits<T>::zero();
    m_index.resize(0);
}
template <typename T>
void indexed_vector<T>::erase_from_index(unsigned j) {
    auto it = std::find(m_index.begin(), m_index.end(), j);
    if (it != m_index.end())
        m_index.erase(it);
}

template <typename T>
void indexed_vector<T>::erase(unsigned j) {
    auto it = std::find(m_index.begin(), m_index.end(), j);
    if (it != m_index.end()) {
        m_data[j] = 0;
        m_index.erase(it);
    }
}


template <typename T>
void indexed_vector<T>::print(std::ostream & out) {
    out << "m_index " << std::endl;
    for (unsigned i = 0; i < m_index.size(); i++) {
        out << m_index[i] << " ";
    }
    out << std::endl;
    print_vector(m_data, out);
}

}
