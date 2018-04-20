/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>
    Creates the Hermite Normal Form of a matrix in place.
Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#include "util/lp/numeric_pair.h"
#include "util/ext_gcd.h"
namespace lp {
template <typename M> // M is the matrix type
class hnf {
    M &          m_A;
    vector<mpq>  m_buffer;
    unsigned     m_m;
    unsigned     m_n;

    void buffer_p_col_i_plus_q_col_j(const mpq & p, unsigned i, const mpq & q, unsigned j) {
        for (unsigned k = i; k < m_n; k++) {
            m_buffer[k] = p * m_A[k][i] + q * m_A[k][j];
        }
    }

    void replace_column_j_by_col(mpq u, unsigned i, mpq v, unsigned j) {
        lp_assert(is_zero(u * m_A[i][i] + v * m_A[i][j]));
        m_A[i][j] = zero_of_type<mpq>();
        for (unsigned k = i + 1; k < m_n; k ++)
            m_A[k][j] = u * m_A[k][i] + v * m_A[k][j];
                  
    }

    void copy_buffer_to_col_i(unsigned i) {
        for (unsigned k = i; k < m_n; k++)
            m_A[k][i] = m_buffer[k];
    }
    
    void handle_column_ij_in_row_i(unsigned i, unsigned j) {
        mpq aii = m_A[i][i];
        mpq aij = m_A[i][j];
        mpq p,q,r;
        extended_gcd(aii, aij, r, p, q);
        buffer_p_col_i_plus_q_col_j(p, i, q, j);
        replace_column_j_by_col(-aij/r, i, aii/r, j);
        copy_buffer_to_col_i(i);
    }
    
    void process_row_column(unsigned i, unsigned j){ 
        if (is_zero(m_A[i][j]))
            return;
        while (j < m_n) {
            handle_column_ij_in_row_i(i, j);
            j++;
        }
        m_A.print(std::cout);
        // continue step 3 here
    }
    
    void process_row(unsigned i) {
        for (unsigned j = i + 1; j < m_n; j++)
            process_row_column(i, j);
    }
    
    void calculate() {
        m_A.print(std::cout);
        std::cout << "working" << std::endl;
        for (unsigned i = 0; i < m_m; i++) {
            process_row(i);
        }
    }
    
public:
    hnf(M & A) : m_A(A),
                 m_buffer(A.column_count()),
                 m_m(m_A.row_count()),
                 m_n(m_A.column_count()) {
        calculate();
    }
};
}
