/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_arith_kernel.cpp

Abstract:

    Compute kernel of a matrix

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "muz/spacer/spacer_arith_kernel.h"

using namespace spacer;

bool spacer_arith_kernel::compute_kernel() {
    SASSERT(m_matrix.num_rows() > 1);

    if (m_matrix.compute_linear_deps(m_kernel)) {
        // the matrix cannot be reduced further
        if (m_matrix.num_cols() - m_kernel.num_rows() <= 1) return true;

        m_kernel.reset(m_kernel.num_cols());
        SASSERT(m_matrix.num_cols() > 2);
    }
    if (m_matrix.num_cols() > 2) m_st.m_failed++;
    if (m_plugin && m_matrix.num_cols() > 2) {
        return m_plugin->compute_kernel(m_matrix, m_kernel);
    }
    return false;
}

