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
#include "util/vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/lp_settings.h"
namespace lp {

template <typename T>
void print_sparse_vector(const vector<T> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++) {
        if (is_zero(t[i]))continue;
        out << "[" << i << "] = " << t[i] << ", ";
    }
    out << std::endl;
}

void print_vector_as_doubles(const vector<mpq> & t, std::ostream & out) {
    for (unsigned i = 0; i < t.size(); i++)
        out << t[i].get_double() << std::setprecision(3) << " ";
    out << std::endl;
}

template <typename T>
void indexed_vector<T>::resize(unsigned data_size) {
    clear();
    m_data.resize(data_size, numeric_traits<T>::zero());
    lp_assert(is_OK());
}

template <typename T>
void indexed_vector<T>::set_value(const T& value, unsigned index) {
    m_data[index] = value;
    lp_assert(std::find(m_index.begin(), m_index.end(), index) == m_index.end());
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
    unsigned i = m_data.size();
    while (i--)  m_data[i] = numeric_traits<T>::zero();
    m_index.resize(0);
}
template <typename T>
void indexed_vector<T>::erase_from_index(unsigned j) {
    auto it = std::find(m_index.begin(), m_index.end(), j);
    if (it != m_index.end())
        m_index.erase(it);
}

#ifdef Z3DEBUG
template <typename T>
bool indexed_vector<T>::is_OK() const {
    return true;
    const double drop_eps = 1e-14;
    for (unsigned i = 0; i < m_data.size(); i++) {
        if (!is_zero(m_data[i]) && lp_settings::is_eps_small_general(m_data[i], drop_eps)) {
            return false;
        }
        if (lp_settings::is_eps_small_general(m_data[i], drop_eps) != (std::find(m_index.begin(), m_index.end(), i) == m_index.end())) {
            return false;
        }
    }

    std::unordered_set<unsigned> s;
    for (unsigned i : m_index) {
        //no duplicates!!!
        if (s.find(i) != s.end())
            return false;
        s.insert(i);
        if (i >= m_data.size())
            return false;
    }

    return true;
}
#endif
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
