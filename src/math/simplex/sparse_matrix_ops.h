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
        static void kernel(sparse_matrix<mpq_ext>& M, vector<vector<rational>>& K) {
            rational D;
            vector<unsigned> d, c;
            unsigned n = M.num_vars(), m = M.num_rows();
            auto& mgr = M.get_manager();
            c.resize(m, 0u);
            d.resize(n, 0u);

            for (unsigned k = 0; k < n; ++k) {
                d[k] = 0;
                for (auto [row, row_entry] : M.get_rows(k)) {
                    if (c[row.id()] != 0)
                        continue;                    
                    auto& m_jk = row_entry->m_coeff;
                    if (mpq_manager<false>::is_zero(m_jk))
                        continue;
                    D = rational(-1) / m_jk;
                    M.mul(row, D.to_mpq());
                    for (auto [row_i, row_i_entry] : M.get_rows(k)) {
                        if (row_i.id() == row.id())
                            continue;                        
                        auto& m_ik = row_i_entry->m_coeff;
                        // row_i += m_ik * row
                        M.add(row_i, m_ik, row);                        
                    }                    
                    c[row.id()] = k + 1;
                    d[k] = row.id() + 1;
                    break;
                }
            }

            for (unsigned k = 0; k < n; ++k) {
                if (d[k] != 0)
                    continue;
                K.push_back(vector<rational>());
                for (unsigned i = 0; i < n; ++i) {
                    if (d[i] > 0) {
                        auto r = sparse_matrix<mpq_ext>::row(d[i]-1);
                        K.back().push_back(rational(M.get_coeff(r, k)));
                    }
                    else if (i == k)
                        K.back().push_back(rational(1));
                    else
                        K.back().push_back(rational(0));
                }
            }

        }

    };


}

