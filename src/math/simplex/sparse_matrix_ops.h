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
            mpq_ext::numeral coeff;
            rational D;
            vector<unsigned> d, c;
            unsigned m = M.num_vars();
            auto& mgr = M.get_manager();
            for (unsigned v = 0; v < m; ++v)
                c.push_back(0);

            unsigned nullity = 0, rank = 0;
            for (auto const& row : M.get_rows()) {
                // scan for non-zero variable in row
                bool found = false;
                d.push_back(0);
                ++nullity;
                for (auto& [coeff1, v] : M.get_row(row)) {
                    if (mpq_manager<false>::is_zero(coeff1))
                        continue;
                    if (c[v] != 0)
                        continue;
                    --nullity;
                    ++rank;
                    d.back() = v + 1;
                    c[v] = row.id() + 1;
                    D = rational(-1) / coeff1;
                    mgr.set(coeff1, mpq(-1));
                    // eliminate v from other rows.
                    for (auto [row2, row_entry2] : M.get_rows(v)) {
                        if (row.id() >= row2.id())
                            continue;
                        mpq & m_js = row_entry2->m_coeff;
                        mgr.set(m_js, (D * m_js).to_mpq());
                    }
                    for (auto& [m_ik, w] : M.get_row(row)) {
                        if (v == w)
                            continue;
                        D = m_ik;
                        mgr.set(m_ik, mpq(0));
                        for (auto [row2, row_entry2] : M.get_rows(w)) {
                            if (row.id() >= row2.id())
                                continue;
                            auto& m_js = M.get_coeff(row2, v);
                            auto & m_is = row_entry2->m_coeff;
                            mgr.set(m_is, (m_is + D * m_js).to_mpq());
                        }
                    }
                    break;
                }                
            }

            mgr.del(coeff);

            std::cout << "nullity " << nullity << "\n";
            std::cout << "rank " << rank << "\n";
            unsigned_vector pivots(rank, 0u);
            unsigned_vector nonpivots(nullity, 0u);

            

            // TODO: extract kernel using d
            for (unsigned k = 0; k < d.size(); ++k) {
                if (d[k] != 0)
                    continue;
                K.push_back(vector<rational>());
                for (unsigned i = 0; i < d.size(); ++i) {
                    if (d[i] > 0) {
                        // row r = row(i);
                        // K.back().push_back(M[d[i]-1][k]);
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

