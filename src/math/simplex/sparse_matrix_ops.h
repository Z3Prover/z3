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
            rational D1, D2;
            vector<unsigned> d, c;
            unsigned m = M.num_vars();
            auto& mgr = M.get_manager();
            for (unsigned v = 0; v < m; ++v)
                c.push_back(0);
            
            for (auto const& row : M.get_rows()) {
                // scan for non-zero variable in row
                bool found = false;
                d.push_back(0);
                for (auto& [coeff1, v] : M.get_row(row)) {
                    if (mpq_manager<false>::is_zero(coeff1))
                        continue;
                    if (c[v] != 0)
                        continue;
                    d.back() = v + 1;
                    c[v] = row.id() + 1;
                    D1 = rational(-1) / coeff1;
                    mgr.set(coeff1, mpq(-1));
                    // eliminate v from other rows.
                    for (auto const& [row2, row_entry2] : M.get_rows(v)) {
                        if (row.id() >= row2.id() || row_entry2->m_coeff == 0)
                            continue;
                        for (auto& [coeff2, w] : M.get_row(row2)) {
                            if (v == w)
                                mgr.set(coeff2, (D1*coeff2).to_mpq());
                        }                        
                    }
                    
                    for (auto& [coeff2, w] : M.get_row(row)) {
                        if (v == w)
                            continue;
                        D2 = coeff2;
                        mgr.set(coeff2, mpq(0));
                        for (auto const& [row2, row_entry2] : M.get_rows(w)) {
                            if (row.id() >= row2.id() || row_entry2->m_coeff == 0 || row_entry2->m_var == v)
                                continue;
                            // mgr.set(row_entry2->m_coeff, row_entry2->m_coeff + D2*row2[v]);
                        }
                    }
                    break;
                }                
            }

            mgr.del(coeff);

            // TODO: extract kernel using d
            for (unsigned k = 0; k < d.size(); ++k) {
                if (d[k] != 0)
                    continue;
                K.push_back(vector<rational>());
                for (unsigned i = 0; i < d.size(); ++i) {                    
                    // K.back().push_back(d[i] > 0 ? M[d[i]-1][k] : (i == k) ? 1 : 0);
                }
            }

        }
    };


}

