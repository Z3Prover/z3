/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_matrix.cpp

Abstract:
    a matrix

Author:
    Bernhard Gleiss

Revision History:


--*/
#include "muz/spacer/spacer_matrix.h"

namespace spacer {
spacer_matrix::spacer_matrix(unsigned m, unsigned n)
    : m_num_rows(m), m_num_cols(n) {
    m_matrix.reserve(m_num_rows);
    for (unsigned i = 0; i < m_num_rows; ++i) {
        m_matrix[i].reserve(m_num_cols, rational(0));
    }
}

void spacer_matrix::get_col(unsigned i, vector<rational> &row) const {
    SASSERT(i < m_num_cols);
    row.reset();
    row.reserve(m_num_rows);
    unsigned j = 0;
    for (auto &v : m_matrix) { row[j++] = (v.get(i)); }
    SASSERT(row.size() == m_num_rows);
}

void spacer_matrix::add_row(const vector<rational> &row) {
    SASSERT(row.size() == m_num_cols);
    m_matrix.push_back(row);
    m_num_rows = m_matrix.size();
}

unsigned spacer_matrix::perform_gaussian_elimination() {
    unsigned i = 0;
    unsigned j = 0;
    while (i < m_matrix.size() && j < m_matrix[0].size()) {
        // find maximal element in column with row index bigger or equal i
        rational max = m_matrix[i][j];
        unsigned max_index = i;

        for (unsigned k = i + 1; k < m_matrix.size(); ++k) {
            if (max < m_matrix[k][j]) {
                max = m_matrix[k][j];
                max_index = k;
            }
        }

        if (max.is_zero()) // skip this column
        {
            ++j;
        } else {
            // reorder rows if necessary
            vector<rational> tmp = m_matrix[i];
            m_matrix[i] = m_matrix[max_index];
            m_matrix[max_index] = m_matrix[i];

            // normalize row
            rational pivot = m_matrix[i][j];
            if (!pivot.is_one()) {
                for (unsigned k = 0; k < m_matrix[i].size(); ++k) {
                    m_matrix[i][k] = m_matrix[i][k] / pivot;
                }
            }

            // subtract row from all other rows
            for (unsigned k = 1; k < m_matrix.size(); ++k) {
                if (k != i) {
                    rational factor = m_matrix[k][j];
                    for (unsigned l = 0; l < m_matrix[k].size(); ++l) {
                        m_matrix[k][l] =
                            m_matrix[k][l] - (factor * m_matrix[i][l]);
                    }
                }
            }

            ++i;
            ++j;
        }
    }

    if (get_verbosity_level() >= 1) { SASSERT(m_matrix.size() > 0); }

    return i; // i points to the row after the last row which is non-zero
}

std::ostream &spacer_matrix::display(std::ostream &out) const {
    out << "Matrix\n";
    for (const auto &row : m_matrix) {
        for (const auto &element : row) { out << element << ", "; }
        out << "\n";
    }
    out << "\n";
    return out;
}

void spacer_matrix::normalize() {
    rational den = rational::one();
    for (unsigned i = 0; i < m_num_rows; ++i) {
        for (unsigned j = 0; j < m_num_cols; ++j) {
            den = lcm(den, denominator(m_matrix[i][j]));
        }
    }

    for (unsigned i = 0; i < m_num_rows; ++i) {
        for (unsigned j = 0; j < m_num_cols; ++j) {
            m_matrix[i][j] = den * m_matrix[i][j];
            SASSERT(m_matrix[i][j].is_int());
        }
    }
}

// attempt to guess that all rows of the matrix are linearly dependent
bool spacer_matrix::is_lin_reltd(unsigned i, unsigned j, rational &coeff1,
                                 rational &coeff2, rational &off) const {
    SASSERT(m_num_rows > 1);
    coeff1 = m_matrix[0][j] - m_matrix[1][j];
    coeff2 = m_matrix[1][i] - m_matrix[0][i];
    off = (m_matrix[0][i] * m_matrix[1][j]) - (m_matrix[1][i] * m_matrix[0][j]);

    for (unsigned k = 0; k < m_num_rows; k++) {
        if (((coeff1 * m_matrix[k][i]) + (coeff2 * m_matrix[k][j]) + off) !=
            rational::zero()) {
            TRACE("cvx_dbg_verb",
                  tout << "Didn't work for " << m_matrix[k][i] << " and "
                       << m_matrix[k][j] << " with coefficients " << coeff1
                       << " , " << coeff2 << " and offset " << off << "\n";);
            return false;
        }
    }

    rational div = gcd(coeff1, gcd(coeff2, off));
    if (div == 0) return false;
    coeff1 = coeff1 / div;
    coeff2 = coeff2 / div;
    off = off / div;
    return true;
}

bool spacer_matrix::compute_linear_deps(spacer_matrix &eq) const {
    SASSERT(m_num_rows > 1);

    eq.reset(m_num_cols + 1);

    rational coeff1, coeff2, off;
    vector<rational> lin_dep;
    lin_dep.reserve(m_num_cols + 1);

    for (unsigned i = 0; i < m_num_cols; i++) {
        for (unsigned j = i + 1; j < m_num_cols; j++) {
            if (is_lin_reltd(i, j, coeff1, coeff2, off)) {
                SASSERT(!(coeff1 == 0 && coeff2 == 0 && off == 0));
                lin_dep[i] = coeff1;
                lin_dep[j] = coeff2;
                lin_dep[m_num_cols] = off;
                eq.add_row(lin_dep);

                TRACE("cvx_dbg_verb", {
                    tout << "Adding row ";
                    for (rational r : lin_dep) tout << r << " ";
                    tout << "\n";
                });
                // reset everything
                lin_dep[i] = rational::zero();
                lin_dep[j] = rational::zero();
                lin_dep[m_num_cols] = 0;
                // Found a dependency for this row, move on.
                // sound because of transitivity of is_lin_reltd
                break;
            }
        }
    }
    return eq.num_rows() > 0;
}
} // namespace spacer
