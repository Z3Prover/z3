/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <algorithm>
#include "util/lp/scaler.h"
#include "util/lp/numeric_pair.h"
namespace lean {
// for scaling an LP
template <typename T, typename X> T scaler<T, X>::right_side_balance() {
    T ret = zero_of_type<T>();
    unsigned i = m_A.row_count();
    while (i--) {
        T rs = abs(convert_struct<T, X>::convert(m_b[i]));
        if (!is_zero<T>(rs)) {
            numeric_traits<T>::log(rs);
            ret += rs * rs;
        }
    }
    return ret;
}

template <typename T, typename X>    T scaler<T, X>::A_min() const {
    T min = zero_of_type<T>();
    for (unsigned i = 0; i < m_A.row_count(); i++) {
        T t = m_A.get_min_abs_in_row(i);
        min = i == 0 ? t : std::min(t, min);
    }
    return min;
}

template <typename T, typename X>    T scaler<T, X>::A_max() const {
    T max = zero_of_type<T>();
    for (unsigned i = 0; i < m_A.row_count(); i++) {
        T t = m_A.get_max_abs_in_row(i);
        max = i == 0? t : std::max(t, max);
    }
    return max;
}

template <typename T, typename X>    T scaler<T, X>::get_A_ratio() const {
    T min = A_min();
    T max = A_max();
    lean_assert(!m_settings.abs_val_is_smaller_than_zero_tolerance(min));
    T ratio = max / min;
    return ratio;
}

template <typename T, typename X>    T scaler<T, X>::get_max_ratio_on_rows() const {
    T ret = T(1);
    unsigned i = m_A.row_count();
    while (i--) {
        T den = m_A.get_min_abs_in_row(i);
        lean_assert(!m_settings.abs_val_is_smaller_than_zero_tolerance(den));
        T t = m_A.get_max_abs_in_row(i)/ den;
        if (t > ret)
            ret = t;
    }
    return ret;
}

template <typename T, typename X>    T scaler<T, X>::get_max_ratio_on_columns() const {
    T ret = T(1);
    unsigned i = m_A.column_count();
    while (i--) {
        T den = m_A.get_min_abs_in_column(i);
        if (m_settings.abs_val_is_smaller_than_zero_tolerance(den))
            continue; // got a zero column
        T t = m_A.get_max_abs_in_column(i)/den;
        if (t > ret)
            ret = t;
    }
    return ret;
}

template <typename T, typename X>    void scaler<T, X>::scale_rows_with_geometric_mean() {
    unsigned i = m_A.row_count();
    while (i--) {
        T max = m_A.get_max_abs_in_row(i);
        T min = m_A.get_min_abs_in_row(i);
        lean_assert(max > zero_of_type<T>() && min > zero_of_type<T>());
        if (is_zero(max) || is_zero(min))
            continue;
        T gm = T(sqrt(numeric_traits<T>::get_double(max*min)));
        if (m_settings.is_eps_small_general(gm, 0.01)) {
            continue;
        }
        m_A.multiply_row(i, one_of_type<T>() / gm);
        m_b[i] /= gm;
    }
}

template <typename T, typename X>    void scaler<T, X>::scale_columns_with_geometric_mean() {
    unsigned i = m_A.column_count();
    while (i--) {
        T max = m_A.get_max_abs_in_column(i);
        T min = m_A.get_min_abs_in_column(i);
        T den = T(sqrt(numeric_traits<T>::get_double(max*min)));
        if (m_settings.is_eps_small_general(den, 0.01))
            continue; // got a zero column
        T gm = T(1)/ den;
        T cs = m_column_scale[i] * gm;
        if (m_settings.is_eps_small_general(cs, 0.1))
            continue;
        m_A.multiply_column(i, gm);
        m_column_scale[i] = cs;
    }
}

template <typename T, typename X>    void scaler<T, X>::scale_once_for_ratio() {
    T max_ratio_on_rows = get_max_ratio_on_rows();
    T max_ratio_on_columns = get_max_ratio_on_columns();
    bool scale_rows_first = max_ratio_on_rows > max_ratio_on_columns;
    // if max_ratio_on_columns is the largerst then the rows are in worser shape then columns
    if (scale_rows_first) {
        scale_rows_with_geometric_mean();
        scale_columns_with_geometric_mean();
    } else {
        scale_columns_with_geometric_mean();
        scale_rows_with_geometric_mean();
    }
}

template <typename T, typename X>    bool scaler<T, X>::scale_with_ratio() {
    T ratio = get_A_ratio();
    // The ratio is greater than or equal to one. We would like to diminish it and bring it as close to 1 as possible
    unsigned reps = m_settings.reps_in_scaler;
    do {
        scale_once_for_ratio();
        T new_r = get_A_ratio();
        if (new_r >= T(0.9) * ratio)
            break;
    } while (reps--);

    bring_rows_and_columns_maximums_to_one();
    return true;
}

template <typename T, typename X>    void scaler<T, X>::bring_row_maximums_to_one() {
    unsigned i = m_A.row_count();
    while (i--) {
        T t = m_A.get_max_abs_in_row(i);
        if (m_settings.abs_val_is_smaller_than_zero_tolerance(t)) continue;
        m_A.multiply_row(i, one_of_type<T>() / t);
        m_b[i] /= t;
    }
}

template <typename T, typename X>    void scaler<T, X>::bring_column_maximums_to_one() {
    unsigned i = m_A.column_count();
    while (i--) {
        T max = m_A.get_max_abs_in_column(i);
        if (m_settings.abs_val_is_smaller_than_zero_tolerance(max)) continue;
        T t = T(1) / max;
        m_A.multiply_column(i, t);
        m_column_scale[i] *= t;
    }
}

template <typename T, typename X>    void scaler<T, X>::bring_rows_and_columns_maximums_to_one() {
    if (get_max_ratio_on_rows() > get_max_ratio_on_columns()) {
        bring_row_maximums_to_one();
        bring_column_maximums_to_one();
    } else {
        bring_column_maximums_to_one();
        bring_row_maximums_to_one();
    }
}

template <typename T, typename X>    bool scaler<T, X>::scale_with_log_balance() {
    T balance = get_balance();
    T balance_before_scaling = balance;
    // todo : analyze the scale order : rows-columns, or columns-rows. Iterate if needed
    for (int i = 0; i < 10; i++) {
        scale_rows();
        scale_columns();
        T nb = get_balance();
        if (nb < T(0.9) * balance) {
            balance = nb;
        } else {
            balance = nb;
            break;
        }
    }
    return balance <= balance_before_scaling;
}
// Returns true if and only if the scaling was successful.
// It is the caller responsibility to restore the matrix
template <typename T, typename X>    bool scaler<T, X>::scale() {
    if (numeric_traits<T>::precise())  return true;
    if (m_settings.scale_with_ratio)
        return scale_with_ratio();
    return scale_with_log_balance();
}

template <typename T, typename X>    void scaler<T, X>::scale_rows() {
    for (unsigned i = 0; i < m_A.row_count(); i++)
        scale_row(i);
}

template <typename T, typename X>    void scaler<T, X>::scale_row(unsigned i) {
    T row_max = std::max(m_A.get_max_abs_in_row(i), abs(convert_struct<T, X>::convert(m_b[i])));
    T alpha = numeric_traits<T>::one();
    if (numeric_traits<T>::is_zero(row_max)) {
        return;
    }
    if (numeric_traits<T>::get_double(row_max) < m_scaling_minimum) {
        do {
            alpha *= 2;
            row_max *= 2;
        } while (numeric_traits<T>::get_double(row_max) < m_scaling_minimum);
        m_A.multiply_row(i, alpha);
        m_b[i] *= alpha;
    } else if (numeric_traits<T>::get_double(row_max) > m_scaling_maximum) {
        do {
            alpha /= 2;
            row_max /= 2;
        } while (numeric_traits<T>::get_double(row_max) > m_scaling_maximum);
        m_A.multiply_row(i, alpha);
        m_b[i] *= alpha;
    }
}

template <typename T, typename X>    void scaler<T, X>::scale_column(unsigned i) {
    T column_max = m_A.get_max_abs_in_column(i);
    T alpha = numeric_traits<T>::one();

    if (numeric_traits<T>::is_zero(column_max)){
        return; // the column has zeros only
    }

    if (numeric_traits<T>::get_double(column_max) < m_scaling_minimum) {
        do {
            alpha *= 2;
            column_max *= 2;
        } while (numeric_traits<T>::get_double(column_max) < m_scaling_minimum);
    } else if (numeric_traits<T>::get_double(column_max) > m_scaling_maximum) {
        do {
            alpha /= 2;
            column_max /= 2;
        } while (numeric_traits<T>::get_double(column_max) > m_scaling_maximum);
    } else {
        return;
    }
    m_A.multiply_column(i, alpha);
    m_column_scale[i] = alpha;
}

template <typename T, typename X>    void scaler<T, X>::scale_columns() {
    for (unsigned i = 0; i < m_A.column_count(); i++) {
        scale_column(i);
    }
}
}
