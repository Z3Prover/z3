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
#include "util/debug.h"
#include <string>
#include <iomanip>
#include "util/lp/lp_utils.h"
#include "util/lp/lp_settings.h"
#include <unordered_set>
namespace lp {

template <typename T> void print_vector(const vector<T> & t, std::ostream & out);
template <typename T> void print_vector(const buffer<T> & t, std::ostream & out);
template <typename T> void print_sparse_vector(const vector<T> & t, std::ostream & out);

void print_vector(const vector<mpq> & t, std::ostream & out);
template <typename T>
class indexed_vector {
public:
    // m_index points to non-zero elements of m_data
    vector<T> m_data;
    vector<unsigned> m_index;
    indexed_vector(unsigned data_size) {
        m_data.resize(data_size, numeric_traits<T>::zero());
    }

    indexed_vector& operator=(const indexed_vector<T>& y) {
        for (unsigned i: m_index)
            m_data[i] = zero_of_type<T>();

        m_index = y.m_index;

        m_data.resize(y.data_size());
        for (unsigned i : m_index)
            m_data[i] = y[i];
        return *this;
    }

    bool operator==(const indexed_vector<T>& y) const {
        std::unordered_set<unsigned> y_index;
        for (unsigned i : y.m_index)
            y_index.insert(i);

        std::unordered_set<unsigned> this_index;
        for (unsigned i : m_index)
            this_index.insert(i);

        for (unsigned i : y.m_index) {
            if (this_index.find(i) == this_index.end())
                return false;
        }
           
        for (unsigned i : m_index) {
            if (y_index.find(i) == y_index.end())
                return false;
        }

        return vectors_are_equal(m_data, m_data);

    }

    indexed_vector() {}

    void resize(unsigned data_size);
    unsigned data_size() const {
        return m_data.size();
    }

    unsigned size() {
        return m_index.size();
    }

    void set_value(const T& value, unsigned index);
    void set_value_as_in_dictionary(unsigned index) {
        SASSERT(index < m_data.size());
        T & loc = m_data[index];
        if (is_zero(loc)) {
            m_index.push_back(index);
            loc = one_of_type<T>(); // use as a characteristic function
        } 
    }
    

    void clear();
    void clear_all();
    const T& operator[] (unsigned i) const {
        return m_data[i];
    }

    T& operator[] (unsigned i)  {
        return m_data[i];
    }

    void clean_up() {
#if 0==1
        for (unsigned k = 0; k < m_index.size(); k++) {
            unsigned i = m_index[k];
            T & v = m_data[i];
            if (lp_settings::is_eps_small_general(v, 1e-14)) {
                v = zero_of_type<T>();
                m_index.erase(m_index.begin() + k--);
            }
        }
#endif
       vector<unsigned> index_copy;
       for (unsigned i : m_index) {
           T & v = m_data[i];
           if (!lp_settings::is_eps_small_general(v, 1e-14)) {
               index_copy.push_back(i);
           } else if (!numeric_traits<T>::is_zero(v)) {
               v = zero_of_type<T>();
           }
       }
       m_index = index_copy;
    }

    
    void erase_from_index(unsigned j);

    void add_value_at_index_with_drop_tolerance(unsigned j, const T& val_to_add) {
        T & v = m_data[j];
        bool was_zero = is_zero(v);
        v += val_to_add;
        if (lp_settings::is_eps_small_general(v, 1e-14)) {
            v = zero_of_type<T>();
            if (!was_zero) {
                erase_from_index(j);
            }
        } else {
            if (was_zero)
                m_index.push_back(j);
        }
    }

    void add_value_at_index(unsigned j, const T& val_to_add) {
        T & v = m_data[j];
        bool was_zero = is_zero(v);
        v += val_to_add;
        if (is_zero(v)) {
            if (!was_zero)
                erase_from_index(j);
        } else {
            if (was_zero)
                m_index.push_back(j);
        }
    }

    void restore_index_and_clean_from_data() {
        m_index.resize(0);
        for (unsigned i = 0; i < m_data.size(); i++) {
            T & v = m_data[i];
            if (lp_settings::is_eps_small_general(v, 1e-14)) {
                v = zero_of_type<T>();
            } else {
                m_index.push_back(i);
            }
        }
    }
    
#ifdef Z3DEBUG
    bool is_OK() const;
    void print(std::ostream & out);
#endif
};
}
