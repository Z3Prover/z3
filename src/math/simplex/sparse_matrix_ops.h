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
        static void kernel(sparse_matrix<mpq_ext>& M, vector<vector<mpq>>& K) {
            mpq_ext::numeral coeff;
            vector<unsigned> d;
            bool_vector c;
            unsigned m = M.num_vars();
            for (unsigned v = 0; v < m; ++v)
                c.push_back(false);
            
            for (auto const& row : M.get_rows()) {
                // scan for non-zero variable in row
                bool found = false;
                d.push_back(0);
                for (auto const& [coeff1, v] : M.get_row(row)) {
                    if (mpq_manager<false>::is_zero(coeff1))
                        continue;
                    if (c[v])
                        continue;
                    d.back() = v + 1;
                    c[v] = true;
                    // eliminate v from other rows.
                    for (auto const& [row2, row_entry2] : M.get_rows(v)) {
                        if (row.id() == row2.id())
                            continue;
                        if (row_entry2->m_coeff == 0)
                            continue;
                        M.get_manager().set(coeff, (- row_entry2->m_coeff / coeff1).to_mpq());
                        M.add(row2, coeff, row);
                    }
                    break;
                }                
            }

            M.get_manager().del(coeff);

            // TODO: extract kernel using d
            for (unsigned k = 0; k < d.size(); ++k) {
                if (d[k] != 0)
                    continue;
                K.push_back(vector<mpq>());
                for (unsigned i = 0; i < d.size(); ++i) {                    
                    // K.back().push_back(d[i] > 0 ? M[d[i]-1][k] : (i == k) ? 1 : 0);
                }
            }

        }
    };


}

