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
        static void gauss_jordan(sparse_matrix<mpq_ext>& M) {
            mpq_ext::numeral coeff;
            vector<unsigned> c, d;
            unsigned m = M.num_vars();
            for (unsigned v = 0; v < m; ++v)
                c.push_back(0);
            
            for (auto const& row : M.get_rows()) {
                // scan for non-zero variable in row
                bool found = false;
                for (auto const& [coeff1, v] : M.get_row(row)) {
                    if (mpq_manager<false>::is_zero(coeff1))
                        continue;
                    found = true;
                    d.push_back(v);
                    c[v] = row.id() + 1;
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
                if (!found)
                    d.push_back(0);
                
            }

            M.get_manager().del(coeff);

            // TODO: do something with c and d
        }
    };


}

