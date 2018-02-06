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
#ifndef _SPACER_MATRIX_H_
#define _SPACER_MATRIX_H_

#include "util/rational.h"
#include "util/vector.h"

namespace spacer {

    class spacer_matrix {
    public:
        spacer_matrix(unsigned m, unsigned n); // m rows, n columns

        unsigned num_rows();
        unsigned num_cols();

        const rational& get(unsigned i, unsigned j);
        void set(unsigned i, unsigned j, const rational& v);

        unsigned perform_gaussian_elimination();

        void print_matrix();
        void normalize();
    private:
        unsigned m_num_rows;
        unsigned m_num_cols;
        vector<vector<rational>> m_matrix;
    };
}

#endif
