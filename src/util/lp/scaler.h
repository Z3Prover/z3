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
#include <math.h>
#include <algorithm>
#include <stdio.h>      /* printf, fopen */
#include <stdlib.h>     /* exit, EXIT_FAILURE */
#include "util/lp/lp_utils.h"
#include "util/lp/static_matrix.h"
namespace lp {
// for scaling an LP
template <typename T, typename X>
class scaler {
    vector<X> & m_b; // right side
    static_matrix<T, X> &m_A; // the constraint matrix
    const T &  m_scaling_minimum;
    const T & m_scaling_maximum;
    vector<T>& m_column_scale;
    lp_settings & m_settings;
public:
    // constructor
    scaler(vector<X> & b, static_matrix<T, X> &A, const T & scaling_minimum, const T & scaling_maximum, vector<T> & column_scale,
           lp_settings & settings):
        m_b(b),
        m_A(A),
        m_scaling_minimum(scaling_minimum),
        m_scaling_maximum(scaling_maximum),
        m_column_scale(column_scale),
        m_settings(settings) {
        SASSERT(m_column_scale.size() == 0);
        m_column_scale.resize(m_A.column_count(), numeric_traits<T>::one());
    }

    T right_side_balance();

    T get_balance() { return m_A.get_balance(); }

    T A_min() const;

    T A_max() const;

    T get_A_ratio() const;

    T get_max_ratio_on_rows() const;

    T get_max_ratio_on_columns() const;

    void scale_rows_with_geometric_mean();

    void scale_columns_with_geometric_mean();

    void scale_once_for_ratio();

    bool scale_with_ratio();

    void bring_row_maximums_to_one();

    void bring_column_maximums_to_one();

    void bring_rows_and_columns_maximums_to_one();

    bool scale_with_log_balance();
    // Returns true if and only if the scaling was successful.
    // It is the caller responsibility to restore the matrix
    bool scale();

    void scale_rows();

    void scale_row(unsigned i);

    void scale_column(unsigned i);

    void scale_columns();
};
}
