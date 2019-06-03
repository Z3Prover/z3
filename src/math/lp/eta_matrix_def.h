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
#include "math/lp/eta_matrix.h"
namespace lp {

// This is the sum of a unit matrix and a one-column matrix
template <typename T, typename X>
void eta_matrix<T, X>::apply_from_left(vector<X> & w, lp_settings & ) {
    auto & w_at_column_index = w[m_column_index];
    for (auto & it : m_column_vector.m_data) {
        w[it.first] += w_at_column_index * it.second;
    }
    w_at_column_index /= m_diagonal_element;
}
template <typename T, typename X>
template <typename L>
void eta_matrix<T, X>::
apply_from_left_local(indexed_vector<L> & w, lp_settings & settings) {
    const L w_at_column_index = w[m_column_index];
    if (is_zero(w_at_column_index)) return;

    if (settings.abs_val_is_smaller_than_drop_tolerance(w[m_column_index] /= m_diagonal_element)) {
        w[m_column_index] = zero_of_type<L>();
        w.erase_from_index(m_column_index);
    }

    for (auto & it : m_column_vector.m_data) {
        unsigned i = it.first;
        if (is_zero(w[i])) {
            L v = w[i] = w_at_column_index * it.second;
            if (settings.abs_val_is_smaller_than_drop_tolerance(v)) {
                w[i] = zero_of_type<L>();
                continue;
            }
            w.m_index.push_back(i);
        } else  {
            L v = w[i] += w_at_column_index * it.second;
            if (settings.abs_val_is_smaller_than_drop_tolerance(v)) {
                w[i] = zero_of_type<L>();
                w.erase_from_index(i);
            }
        }
    }
}
template <typename T, typename X>
void eta_matrix<T, X>::apply_from_right(vector<T> & w) {
#ifdef Z3DEBUG
    // dense_matrix<T, X> deb(*this);
    // auto clone_w = clone_vector<T>(w, get_number_of_rows());
    // deb.apply_from_right(clone_w);
#endif
    T t = w[m_column_index] / m_diagonal_element;
    for (auto & it : m_column_vector.m_data) {
        t += w[it.first] * it.second;
    }
    w[m_column_index] = t;
#ifdef Z3DEBUG
    // lp_assert(vectors_are_equal<T>(clone_w, w, get_number_of_rows()));
    // delete clone_w;
#endif
}
template <typename T, typename X>
void eta_matrix<T, X>::apply_from_right(indexed_vector<T> & w) {
    if (w.m_index.empty())
        return;
#ifdef Z3DEBUG
    // vector<T> wcopy(w.m_data);
    // apply_from_right(wcopy);
#endif
    T & t = w[m_column_index];
    t /= m_diagonal_element;
    bool was_in_index = (!numeric_traits<T>::is_zero(t));
    
    for (auto & it : m_column_vector.m_data) {
        t += w[it.first] * it.second;
    }

    if (numeric_traits<T>::precise() ) {
        if (!numeric_traits<T>::is_zero(t)) {
            if (!was_in_index)
                w.m_index.push_back(m_column_index);
        } else {
            if (was_in_index)
                w.erase_from_index(m_column_index);
        }
    } else {
        if (!lp_settings::is_eps_small_general(t, 1e-14)) {
            if (!was_in_index)
                w.m_index.push_back(m_column_index);
        } else {
            if (was_in_index)
                w.erase_from_index(m_column_index);
            t = zero_of_type<T>();
        }
    }
    
#ifdef Z3DEBUG
    // lp_assert(w.is_OK());
    // lp_assert(vectors_are_equal<T>(wcopy, w.m_data));
#endif
}
#ifdef Z3DEBUG
template <typename T, typename X>
T eta_matrix<T, X>::get_elem(unsigned i, unsigned j) const {
    if (j == m_column_index){
        if (i == j) {
            return 1 / m_diagonal_element;
        }
        return m_column_vector[i];
    }

    return i == j ? numeric_traits<T>::one() : numeric_traits<T>::zero();
}
#endif
template <typename T, typename X>
void eta_matrix<T, X>::conjugate_by_permutation(permutation_matrix<T, X> & p) {
    // this = p * this * p(-1)
#ifdef Z3DEBUG
    // auto rev = p.get_reverse();
    // auto deb = ((*this) * rev);
    // deb = p * deb;
#endif
    m_column_index = p.get_rev(m_column_index);
    for (auto & pair : m_column_vector.m_data) {
        pair.first = p.get_rev(pair.first);
    }
#ifdef Z3DEBUG
    // lp_assert(deb == *this);
#endif
}
}
