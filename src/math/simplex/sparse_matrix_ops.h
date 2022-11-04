/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sparse_matrix_ops.h

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

--*/

#pragma once

#include "math/simplex/sparse_matrix.h"
#include "util/rational.h"

namespace simplex {

class sparse_matrix_ops {
  public:
    template <typename Ext>
    static void kernel(sparse_matrix<Ext> &M, vector<vector<rational>> &K) {
        using scoped_numeral = typename Ext::scoped_numeral;

        vector<unsigned> d, c;
        unsigned n_vars = M.num_vars(), n_rows = M.num_rows();
        c.resize(n_rows, 0u);
        d.resize(n_vars, 0u);

        auto &m = M.get_manager();
        scoped_numeral m_ik(m);
        scoped_numeral D(m);

        for (unsigned k = 0; k < n_vars; ++k) {
            d[k] = 0;
            for (auto [row, row_entry] : M.get_rows(k)) {
                if (c[row.id()] != 0) continue;
                auto &m_jk = row_entry->m_coeff;
                if (m.is_zero(m_jk)) continue;

                // D = rational(-1) / m_jk;
                m.set(D, m_jk);
                m.inv(D);
                m.neg(D);

                M.mul(row, D);
                for (auto [row_i, row_i_entry] : M.get_rows(k)) {
                    if (row_i.id() == row.id()) continue;
                    m.set(m_ik, row_i_entry->m_coeff);
                    // row_i += m_ik * row
                    M.add(row_i, m_ik, row);
                }
                c[row.id()] = k + 1;
                d[k] = row.id() + 1;
                break;
            }
        }

        for (unsigned k = 0; k < n_vars; ++k) {
            if (d[k] != 0) continue;
            K.push_back(vector<rational>());
            for (unsigned i = 0; i < n_vars; ++i) {
                if (d[i] > 0) {
                    auto r = typename sparse_matrix<Ext>::row(d[i] - 1);
                    K.back().push_back(rational(M.get_coeff(r, k)));
                }
                else if (i == k)
                    K.back().push_back(rational(1));
                else
                    K.back().push_back(rational(0));
            }
        }
    }

    static void kernel(sparse_matrix<mpq_ext> &M, vector<vector<rational>> &K) {
        kernel<mpq_ext>(M, K);
    }

    /// \brief Kernel computation using fraction-free-elimination
    ///
    template <typename Ext>
    static void kernel_ffe(sparse_matrix<Ext> &M, vector<vector<rational>> &K) {
        using scoped_numeral = typename Ext::scoped_numeral;

        /// Based on 	George Nakos, Peter R. Turner, Robert M. Williams:
        /// Fraction-free algorithms for linear and polynomial equations. SIGSAM
        /// Bull. 31(3): 11-19 (1997)
        vector<unsigned> d, c;
        unsigned n_vars = M.num_vars(), n_rows = M.num_rows();
        c.resize(n_rows, 0u);
        d.resize(n_vars, 0u);

        auto &m = M.get_manager();
        scoped_numeral m_ik(m);
        scoped_numeral m_jk(m);
        scoped_numeral last_pv(m);

        m.set(last_pv, 1);

        for (unsigned k = 0; k < n_vars; ++k) {
            d[k] = 0;
            for (auto [row, row_entry] : M.get_rows(k)) {
                if (c[row.id()] != 0) continue;
                auto &m_jk_ref = row_entry->m_coeff;
                if (m.is_zero(m_jk_ref))
                    // XXX: should not happen, the matrix is sparse
                    continue;

                // this a pivot column
                m.set(m_jk, m_jk_ref);

                // ensure that pivot is negative
                if (m.is_pos(m_jk_ref)) { M.neg(row); }
                else { m.neg(m_jk); }
                // m_jk is abs(M[j]][k])

                for (auto row_i : M.get_rows()) {
                    if (row_i.id() == row.id()) continue;

                    m.set(m_ik, M.get_coeff(row_i, k));
                    // row_i *= m_jk
                    M.mul(row_i, m_jk);
                    if (!m.is_zero(m_ik)) {
                        // row_i += m_ik * row
                        M.add(row_i, m_ik, row);
                    }
                    M.div(row_i, last_pv);
                }
                c[row.id()] = k + 1;
                d[k] = row.id() + 1;
                m.set(last_pv, m_jk);
                break;
            }
        }

        for (unsigned k = 0; k < n_vars; ++k) {
            if (d[k] != 0) continue;
            K.push_back(vector<rational>());
            for (unsigned i = 0; i < n_vars; ++i) {
                if (d[i] > 0) {
                    auto r = typename sparse_matrix<Ext>::row(d[i] - 1);
                    K.back().push_back(rational(M.get_coeff(r, k)));
                }
                else if (i == k)
                    K.back().push_back(rational(last_pv));
                else
                    K.back().push_back(rational(0));
            }
        }
    }

    static void kernel_ffe(sparse_matrix<mpq_ext> &M,
                           vector<vector<rational>> &K) {
        kernel_ffe<mpq_ext>(M, K);
    }


    template <typename Ext>
    static void kernel_ffe(sparse_matrix<Ext> &M, sparse_matrix<Ext> &K,
                           vector<unsigned> &basics) {
        using scoped_numeral = typename Ext::scoped_numeral;

        /// Based on 	George Nakos, Peter R. Turner, Robert M. Williams:
        /// Fraction-free algorithms for linear and polynomial equations. SIGSAM
        /// Bull. 31(3): 11-19 (1997)
        vector<unsigned> d, c;
        unsigned n_vars = M.num_vars(), n_rows = M.num_rows();
        c.resize(n_rows, 0u);
        d.resize(n_vars, 0u);

        auto &m = M.get_manager();
        scoped_numeral m_ik(m);
        scoped_numeral m_jk(m);
        scoped_numeral last_pv(m);

        m.set(last_pv, 1);

        for (unsigned k = 0; k < n_vars; ++k) {
            d[k] = 0;
            for (auto [row, row_entry] : M.get_rows(k)) {
                if (c[row.id()] != 0) continue;
                auto &m_jk_ref = row_entry->m_coeff;
                if (m.is_zero(m_jk_ref))
                    // XXX: should not happen, the matrix is sparse
                    continue;

                // this a pivot column
                m.set(m_jk, m_jk_ref);

                // ensure that pivot is negative
                if (m.is_pos(m_jk_ref)) { M.neg(row); }
                else { m.neg(m_jk); }
                // m_jk is abs(M[j]][k])

                for (auto row_i : M.get_rows()) {
                    if (row_i.id() == row.id()) continue;

                    m.set(m_ik, M.get_coeff(row_i, k));
                    // row_i *= m_jk
                    M.mul(row_i, m_jk);
                    if (!m.is_zero(m_ik)) {
                        // row_i += m_ik * row
                        M.add(row_i, m_ik, row);
                    }
                    M.div(row_i, last_pv);
                }
                c[row.id()] = k + 1;
                d[k] = row.id() + 1;
                m.set(last_pv, m_jk);
                break;
            }
        }

        K.ensure_var(n_vars - 1);
        for (unsigned k = 0; k < n_vars; ++k) {
            if (d[k] != 0) continue;
            auto row = K.mk_row();
            basics.push_back(k);
            for (unsigned i = 0; i < n_vars; ++i) {
                if (d[i] > 0) {
                    auto r = typename sparse_matrix<Ext>::row(d[i] - 1);
                    K.add_var(row, M.get_coeff(r, k), i);
                }
                else if (i == k)
                  K.add_var(row, last_pv, i);
            }
        }
    }

};
} // namespace simplex
