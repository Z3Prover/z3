/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_matrix.h

Abstract:
    a matrix

Author:
    Bernhard Gleiss

Revision History:


--*/
#pragma once

#include "util/rational.h"
#include "util/vector.h"

namespace spacer {

class spacer_matrix {
  private:
    unsigned m_num_rows;
    unsigned m_num_cols;
    vector<vector<rational>> m_matrix;

    bool is_lin_reltd(unsigned i, unsigned j, rational &coeff1,
                      rational &coeff2, rational &off) const;

  public:
    spacer_matrix(unsigned m, unsigned n); // m rows, n columns

    unsigned num_rows() const { return m_num_rows; }
    unsigned num_cols() const { return m_num_cols; }

    const rational &get(unsigned i, unsigned j) const { return m_matrix[i][j]; }
    void set(unsigned i, unsigned j, const rational &v) { m_matrix[i][j] = v; }

    const vector<rational> &get_row(unsigned i) const {
        SASSERT(i < num_rows());
        return m_matrix.get(i);
    }

    /// Returns a copy of row \p i
    void get_col(unsigned i, vector<rational> &row) const;

    void add_row(const vector<rational> &row);

    void reset(unsigned n_cols) {
        m_num_rows = 0;
        m_num_cols = n_cols;
        m_matrix.reset();
    }

    std::ostream &display(std::ostream &out) const;
    void normalize();
    unsigned perform_gaussian_elimination();

    bool compute_linear_deps(spacer_matrix &eq) const;
};
} // namespace spacer
