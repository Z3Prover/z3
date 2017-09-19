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
#include "util/lp/row_eta_matrix.h"
namespace lp {
template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_left(vector<X> & w, lp_settings &) {
    // #ifdef Z3DEBUG
    //         dense_matrix<T> deb(*this);
    //         auto clone_w = clone_vector<T>(w, m_dimension);
    //         deb.apply_from_left(clone_w, settings);
    // #endif
    
    auto & w_at_row = w[m_row];
    for (auto & it : m_row_vector.m_data) {
        w_at_row += w[it.first] * it.second;
    }
    // w[m_row] = w_at_row;
    // #ifdef Z3DEBUG
    //         SASSERT(vectors_are_equal<T>(clone_w, w, m_dimension));
    //         delete [] clone_w;
    // #endif
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_left_local_to_T(indexed_vector<T> & w, lp_settings & settings) {
    auto w_at_row = w[m_row];
    bool was_zero_at_m_row = is_zero(w_at_row);

    for (auto & it : m_row_vector.m_data) {
        w_at_row += w[it.first] * it.second;
    }

    if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_row)){
        if (was_zero_at_m_row) {
            w.m_index.push_back(m_row);
        }
        w[m_row] = w_at_row;
    } else if (!was_zero_at_m_row){
        w[m_row] = zero_of_type<T>();
        auto it = std::find(w.m_index.begin(), w.m_index.end(), m_row);
        w.m_index.erase(it);
    }
    // TBD: SASSERT(check_vector_for_small_values(w, settings));
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_left_local_to_X(indexed_vector<X> & w, lp_settings & settings) {
    auto w_at_row = w[m_row];
    bool was_zero_at_m_row = is_zero(w_at_row);

    for (auto & it : m_row_vector.m_data) {
        w_at_row += w[it.first] * it.second;
    }

    if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_row)){
        if (was_zero_at_m_row) {
            w.m_index.push_back(m_row);
        }
        w[m_row] = w_at_row;
    } else if (!was_zero_at_m_row){
        w[m_row] = zero_of_type<X>();
        auto it = std::find(w.m_index.begin(), w.m_index.end(), m_row);
        w.m_index.erase(it);
    }
    // TBD: does not compile SASSERT(check_vector_for_small_values(w, settings));
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_right(vector<T> & w) {
    const T & w_row = w[m_row];
    if (numeric_traits<T>::is_zero(w_row)) return;
#ifdef Z3DEBUG
    // dense_matrix<T> deb(*this);
    // auto clone_w = clone_vector<T>(w, m_dimension);
    // deb.apply_from_right(clone_w);
#endif
    for (auto & it : m_row_vector.m_data) {
        w[it.first] += w_row * it.second;
    }
#ifdef Z3DEBUG
    // SASSERT(vectors_are_equal<T>(clone_w, w, m_dimension));
    // delete clone_w;
#endif
}

template <typename T, typename X>
void row_eta_matrix<T, X>::apply_from_right(indexed_vector<T> & w) {
    SASSERT(w.is_OK());
    const T & w_row = w[m_row];
    if (numeric_traits<T>::is_zero(w_row)) return;
#ifdef Z3DEBUG
    // vector<T> wcopy(w.m_data);
    // apply_from_right(wcopy);
#endif
    if (numeric_traits<T>::precise()) {
        for (auto & it : m_row_vector.m_data) {
            unsigned j = it.first;
            bool was_zero = numeric_traits<T>::is_zero(w[j]);
            const T & v = w[j] += w_row * it.second;       
            
            if (was_zero) {
                if (!numeric_traits<T>::is_zero(v))                     
                    w.m_index.push_back(j);
            } else {
                if (numeric_traits<T>::is_zero(v))
                    w.erase_from_index(j);
            }
        }
    } else { // the non precise version
        const double drop_eps = 1e-14;
        for (auto & it : m_row_vector.m_data) {
            unsigned j = it.first;
            bool was_zero = numeric_traits<T>::is_zero(w[j]);
            T & v = w[j] += w_row * it.second;       
            
            if (was_zero) { 
                if (!lp_settings::is_eps_small_general(v, drop_eps))
                    w.m_index.push_back(j);
                else
                    v = zero_of_type<T>();
            } else {
                if (lp_settings::is_eps_small_general(v, drop_eps)) {
                    w.erase_from_index(j);
                    v = zero_of_type<T>();
                }
            }
        }
    }
#ifdef Z3DEBUG
    // SASSERT(vectors_are_equal(wcopy, w.m_data));

#endif
}

template <typename T, typename X>
void row_eta_matrix<T, X>::conjugate_by_permutation(permutation_matrix<T, X> & p) {
    // this = p * this * p(-1)
#ifdef Z3DEBUG
    // auto rev = p.get_reverse();
    // auto deb = ((*this) * rev);
    // deb = p * deb;
#endif
    m_row = p.apply_reverse(m_row);
    // copy aside the column indices
    vector<unsigned> columns;
    for (auto & it : m_row_vector.m_data)
        columns.push_back(it.first);
    for (unsigned i = static_cast<unsigned>(columns.size()); i-- > 0;)
        m_row_vector.m_data[i].first = p.get_rev(columns[i]);
#ifdef Z3DEBUG
    // SASSERT(deb == *this);
#endif
}
#ifdef Z3DEBUG
template <typename T, typename X>
T row_eta_matrix<T, X>::get_elem(unsigned row, unsigned col) const {
    if (row == m_row){
        if (col == row) {
            return numeric_traits<T>::one();
        }
        return m_row_vector[col];
    }

    return col == row ? numeric_traits<T>::one() : numeric_traits<T>::zero();
}
#endif
}

