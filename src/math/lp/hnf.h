/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>
    Creates the Hermite Normal Form of a matrix in place.
    We suppose that $A$ is an integral $m$ by $n$ matrix or rank $m$, where $n >= m$.
    The paragraph below is applicable to the usage of HNF.
We have $H = AU$ where $H$ is in Hermite Normal Form
and $U$ is a unimodular matrix. We do not have an explicit
 representation of $U$. For a given $i$ we need to find the $i$-th
    row of $U^{-1}$. 
Let $e_i$ be a vector of length $m$ with all elements equal to $0$ and
$1$ at $i$-th position. Then we need to find the row vector $e_iU^{-1}=t$. Noticing that $U^{-1} = H^{-1}A$, we have $e_iH^{-1}A=t$.
We find  $e_iH^{-1} = f$ by solving $e_i = fH$ and then $fA$ gives us $t$.

Author:
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "math/lp/numeric_pair.h"
#include "util/ext_gcd.h"
namespace lp {
namespace hnf_calc {

    // d = u * a + v * b and the sum of abs(u) + abs(v) is minimal, d is positive
inline
void extended_gcd_minimal_uv(const mpq & a, const mpq & b, mpq & d, mpq & u, mpq & v) {
    if (is_zero(a)) {
        u = zero_of_type<mpq>();
        v = one_of_type<mpq>();
        d = b;
        return;
    }
    if (is_zero(b)) {
        u = one_of_type<mpq>();
        v = zero_of_type<mpq>();
        d = a;
        return;
    }
#if 1
    d = gcd(a, b, u, v);
#else
    extended_gcd(a, b, d, u, v);
#endif
    if (is_neg(d)) {
        d = -d;
        u = -u;
        v = -v;
    }

    if (d == a) {
        u = one_of_type<mpq>();
        v = zero_of_type<mpq>();
        return;
    }
    if (d == -a) {
        u = - one_of_type<mpq>();
        v = zero_of_type<mpq>();
        return;
    }
        
    mpq a_over_d = abs(a) / d;
    mpq r;
        
    mpq k = machine_div_rem(v, a_over_d, r);
    if (is_neg(r)) {
        r += a_over_d;
        k -= one_of_type<mpq>();
    }

    lp_assert(v == k * a_over_d + r);

    if (is_pos(b)) {
        v = r - a_over_d; //   v -= (k + 1) * a_over_d;
        lp_assert(- a_over_d < v && v <= zero_of_type<mpq>());

        if (is_pos(a)) {
            u += (k + 1) * (b / d);
            lp_assert( one_of_type<mpq>() <= u && u <= abs(b)/d);
        } else {
            u -= (k + 1) * (b / d);
            lp_assert( one_of_type<mpq>() <= -u && -u <= abs(b)/d);
        }
    } else {
        v = r; // v -= k * a_over_d;
        lp_assert(- a_over_d < -v && -v <= zero_of_type<mpq>());
        if (is_pos(a)) {
            u += k * (b / d);
            lp_assert( one_of_type<mpq>() <= u && u <= abs(b)/d);
        } else {
            u -= k * (b / d);
            lp_assert( one_of_type<mpq>() <= -u && -u <= abs(b)/d);
        }
    }
    lp_assert(d == u * a + v * b);
}



template <typename M> 
bool prepare_pivot_for_lower_triangle(M &m, unsigned r) {
    for (unsigned i = r; i < m.row_count(); i++) {
        for (unsigned j = r; j < m.column_count(); j++) {
            if (!is_zero(m[i][j])) {
                if (i != r) {
                    m.transpose_rows(i, r);
                }
                if (j != r) {
                    m.transpose_columns(j, r);
                }
                return true;
            }
        }
    }
    return false;
}

template <typename M> 
void pivot_column_non_fractional(M &m, unsigned r, bool & overflow, const mpq & big_number) {
    lp_assert(!is_zero(m[r][r]));
    for (unsigned j = r + 1; j < m.column_count(); j++) {
        for (unsigned i = r + 1; i  < m.row_count(); i++) {            
            if (
                (m[i][j] = (r > 0) ? (m[r][r]*m[i][j] - m[i][r]*m[r][j]) / m[r-1][r-1] :
                                     (m[r][r]*m[i][j] - m[i][r]*m[r][j]))
                >= big_number) {
                overflow = true;
                return;
            }
            lp_assert(is_integer(m[i][j]));
        }
    }
}

// returns the rank of the matrix
template <typename M> 
unsigned to_lower_triangle_non_fractional(M &m, bool & overflow, const mpq& big_number) {
    unsigned i = 0;
    for (; i < m.row_count(); i++) {
        if (!prepare_pivot_for_lower_triangle(m, i)) {
            return i;
        }
        pivot_column_non_fractional(m, i, overflow, big_number);
        if (overflow)
            return 0;
    }
    lp_assert(i == m.row_count());
    return i; 
}

// returns gcd of values below diagonal i,i
template <typename M>
mpq gcd_of_row_starting_from_diagonal(const M& m, unsigned i) {
    mpq g = zero_of_type<mpq>();
    unsigned j = i;
    for (; j < m.column_count() && is_zero(g); j++) {
        const auto & t = m[i][j];
        if (!is_zero(t))
            g = abs(t);
    }
    lp_assert(!is_zero(g));
    for (; j < m.column_count(); j++) {
        const auto & t = m[i][j];
        if (!is_zero(t))
            g = gcd(g, t);
    }
    return g;
}

// It fills "r" - the basic rows of m.
// The plan is to transform m to the lower triangular form by using non-fractional Gaussian Elimination by columns.
// Then the trailing after the diagonal elements of the following elements of the last non-zero row of the matrix,
// namely, m[r-1][r-1], m[r-1][r], ..., m[r-1]m[m.column_count() - 1] give the determinants of all minors of rank r.
// The gcd of these minors is the return value.
 
template <typename M> 
mpq determinant_of_rectangular_matrix(const M& m, svector<unsigned> & basis_rows, const mpq& big_number) {
    auto m_copy = m;
    bool overflow = false;
    unsigned rank = to_lower_triangle_non_fractional(m_copy, overflow, big_number);
    if (overflow)
        return big_number;
    if (rank == 0)
        return one_of_type<mpq>();

    for (unsigned i = 0; i < rank; i++) {
        basis_rows.push_back(m_copy.adjust_row(i));
    }
    TRACE("hnf_calc", tout << "basis_rows = "; print_vector(basis_rows, tout); m_copy.print(tout, "m_copy = "););
    return gcd_of_row_starting_from_diagonal(m_copy, rank - 1);
}
} // end of namespace hnf_calc

template <typename M> // M is the matrix type
class hnf {
    // fields

#ifdef Z3DEBUG
    M            m_H;
    M            m_U;
    M            m_U_reverse;
    M            m_A_orig;
#endif
    M            m_W;
    vector<mpq>  m_buffer;
    unsigned     m_m;
    unsigned     m_n;
    mpq          m_d; // it is a positive number and a multiple of gcd of r-minors of m_A_orig, where r is the rank of m_A_orig
    //  we suppose that the rank of m_A is equal to row_count(), and that row_count() <= column_count(), that is m_A has the full rank
    unsigned     m_i;
    unsigned     m_j;
    mpq          m_R;
    mpq          m_half_R;
    mpq mod_R_balanced(const mpq & a) const {
       mpq t = a % m_R;
       return t > m_half_R? t - m_R : (t < - m_half_R? t + m_R : t);
    }

    mpq mod_R(const mpq & a) const {
       mpq t = a % m_R;
       t = is_neg(t) ? t + m_R : t;       
       CTRACE("hnf", is_neg(t), tout << "a=" << a << ", m_R= " << m_R << std::endl;);
       return t;
           
    }

#ifdef Z3DEBUG
    void buffer_p_col_i_plus_q_col_j_H(const mpq & p, unsigned i, const mpq & q, unsigned j) {
        for (unsigned k = i; k < m_m; k++) {
            m_buffer[k] =  p * m_H[k][i] + q * m_H[k][j];
        }
    }
#endif
    bool zeros_in_column_W_above(unsigned i) {
        for (unsigned k = 0; k < i; k++)
            if (!is_zero(m_W[k][i]))
                return false;
        return true;
    }
    
    void buffer_p_col_i_plus_q_col_j_W_modulo(const mpq & p, const mpq & q) {
        lp_assert(zeros_in_column_W_above(m_i));
        for (unsigned k = m_i; k < m_m; k++) {
            m_buffer[k] =  mod_R_balanced(mod_R_balanced(p * m_W[k][m_i]) + mod_R_balanced(q * m_W[k][m_j]));
        }
    }
#ifdef Z3DEBUG
    void buffer_p_col_i_plus_q_col_j_U(const mpq & p, unsigned i, const mpq & q, unsigned j) {
        for (unsigned k = 0; k < m_n; k++) {
            m_buffer[k] = p * m_U[k][i] + q * m_U[k][j];
        }
    }

    void pivot_column_i_to_column_j_H(mpq u, unsigned i, mpq v, unsigned j) {
        lp_assert(is_zero(u * m_H[i][i] + v * m_H[i][j]));
        m_H[i][j] = zero_of_type<mpq>();
        for (unsigned k = i + 1; k < m_m; k ++)
            m_H[k][j] = u * m_H[k][i] + v * m_H[k][j];
                  
    }
#endif
    void pivot_column_i_to_column_j_W_modulo(mpq u, mpq v)  {
        lp_assert(is_zero((u * m_W[m_i][m_i] + v * m_W[m_i][m_j]) % m_R));
        m_W[m_i][m_j] = zero_of_type<mpq>();
        for (unsigned k = m_i + 1; k < m_m; k ++)
            m_W[k][m_j] = mod_R_balanced(mod_R_balanced(u * m_W[k][m_i]) + mod_R_balanced(v * m_W[k][m_j]));
    }

#ifdef Z3DEBUG
    void pivot_column_i_to_column_j_U(mpq u, unsigned i, mpq v, unsigned j) {
        for (unsigned k = 0; k < m_n; k ++)
            m_U[k][j] = u * m_U[k][i] + v * m_U[k][j];
                  
    }

    void copy_buffer_to_col_i_H(unsigned i) {
        for (unsigned k = i; k < m_m; k++) {
            m_H[k][i] = m_buffer[k];
        }
    }
    void copy_buffer_to_col_i_U(unsigned i) {
        for (unsigned k = 0; k < m_n; k++)
            m_U[k][i] = m_buffer[k];
    }

    // multiply by (a, b)
    //             (c, d)
    // from the left where i and j are the modified columns
    // the [i][i] = a, and [i][j] = b for the matrix we multiply by
   
    
    void multiply_U_reverse_from_left_by(unsigned i, unsigned j, const mpq & a, const mpq & b, const mpq & c, const mpq d) {
        // the new i-th row goes to the buffer
        for (unsigned k = 0; k < m_n; k++) {
            m_buffer[k] = a * m_U_reverse[i][k] + b * m_U_reverse[j][k];
        }

        // calculate the new j-th row in place
        for (unsigned k = 0; k < m_n; k++) {
            m_U_reverse[j][k] = c * m_U_reverse[i][k] + d * m_U_reverse[j][k];
        }

        // copy the buffer into i-th row
        for (unsigned k = 0; k < m_n; k++) {
            m_U_reverse[i][k] = m_buffer[k];
        }
    }

    void handle_column_ij_in_row_i(unsigned i, unsigned j) {
        const mpq& aii = m_H[i][i];
        const mpq& aij = m_H[i][j];
        mpq p,q,r;
        extended_gcd(aii, aij, r, p, q);
        mpq aii_over_r = aii / r;
        mpq aij_over_r = aij / r;
        
        
        buffer_p_col_i_plus_q_col_j_H(p, i, q, j);
        pivot_column_i_to_column_j_H(- aij_over_r, i, aii_over_r, j);
        copy_buffer_to_col_i_H(i);

        
        buffer_p_col_i_plus_q_col_j_U(p, i, q, j);
        pivot_column_i_to_column_j_U(- aij_over_r, i, aii_over_r, j);
        copy_buffer_to_col_i_U(i);

        // U was multiplied from the right by (p, - aij_over_r)
        //                                    (q, aii_over_r  )
        // We need to multiply U_reverse by   (aii_over_r, aij_over_r)
        //                                    (-q        , p)
        // from the left
        
        multiply_U_reverse_from_left_by(i, j, aii_over_r, aij_over_r, -q, p);
        CASSERT("hnf_test", is_correct_modulo());
    }
    

    void switch_sign_for_column(unsigned i) {
        for (unsigned k = i; k < m_m; k++)
            m_H[k][i].neg();
        for (unsigned k = 0; k < m_n; k++)
            m_U[k][i].neg();

        // switch sign for the i-th row in the reverse m_U_reverse
        for (unsigned k = 0; k < m_n; k++)
            m_U_reverse[i][k].neg();
        
    }
    
    void process_row_column(unsigned i, unsigned j){
        if (is_zero(m_H[i][j]))
            return;
        handle_column_ij_in_row_i(i, j);
    }

    void replace_column_j_by_j_minus_u_col_i_H(unsigned i, unsigned j, const mpq & u) {
        lp_assert(j < i);
        for (unsigned k = i; k < m_m; k++) {
            m_H[k][j] -= u * m_H[k][i];
        }
    }
    void replace_column_j_by_j_minus_u_col_i_U(unsigned i, unsigned j, const mpq & u) {
        
        lp_assert(j < i);
        for (unsigned k = 0; k < m_n; k++) {
            m_U[k][j] -= u * m_U[k][i];
        }
        // Here we multiply from m_U from the right by the matrix ( 1,  0)
        //                                                        ( -u, 1).
        // To adjust the reverse we multiply it from the left by (1, 0)
        //                                                       (u, 1)

        for (unsigned k = 0; k < m_n; k++) {
            m_U_reverse[i][k] += u * m_U_reverse[j][k];
        }
       
        
    }

    void work_on_columns_less_than_i_in_the_triangle(unsigned i) {
        const mpq & mii = m_H[i][i];
        if (is_zero(mii)) return;
        for (unsigned j = 0; j < i; j++) {
            const mpq & mij = m_H[i][j];
            if (!is_pos(mij) && - mij < mii)
                continue;
            mpq u = ceil(mij / mii);
            replace_column_j_by_j_minus_u_col_i_H(i, j, u);
            replace_column_j_by_j_minus_u_col_i_U(i, j, u);
        }
    }
    
    void process_row(unsigned i) {
        for (unsigned j = i + 1; j < m_n; j++) {
            process_row_column(i, j);
        }
        if (i >= m_n) {
            lp_assert(m_H == m_A_orig * m_U);
            return;
        }
        if (is_neg(m_H[i][i]))
            switch_sign_for_column(i);
        work_on_columns_less_than_i_in_the_triangle(i);
        CASSERT("hnf_test", is_correct_modulo());
    }

    void calculate() {
        for (unsigned i = 0; i < m_m; i++) {
            process_row(i);
        }
    }

    void prepare_U_and_U_reverse() {
        m_U = M(m_H.column_count());
        for (unsigned i = 0; i < m_U.column_count(); i++)
            m_U[i][i] = 1;

        m_U_reverse = m_U;
        
        lp_assert(m_H == m_A_orig * m_U);
    }

    bool row_is_correct_form(unsigned i) const {
        if (i >= m_n)
            return true;
        const mpq& hii = m_H[i][i];
        if (is_neg(hii))
            return false;
        for (unsigned j = 0; j < i; j++) {
            const mpq & hij = m_H[i][j];
            if (is_pos(hij))
                return false;
            if (!is_zero(hii) && - hij >= hii)
                return false;
        }
        
        return true;
    }
    
    bool is_correct_form() const {
        for (unsigned i = 0; i < m_m; i++)
            if (!row_is_correct_form(i))
                return false;
        return true;
    }

    bool is_correct() const {
        return m_H == m_A_orig * m_U && is_unit_matrix(m_U * m_U_reverse);
    }

    bool is_correct_modulo() const {
        return m_H.equal_modulo(m_A_orig * m_U, m_d) && is_unit_matrix(m_U * m_U_reverse);
    }

    bool is_correct_final() const {
        if (!is_correct()) {
            TRACE("hnf_calc",
                  tout << "m_H =            "; m_H.print(tout, 17);
                  tout << "\nm_A_orig * m_U = ";  (m_A_orig * m_U).print(tout, 17);
                  tout << "is_correct() does not hold" << std::endl;);
            return false;
        }
        if (!is_correct_form()) {
            TRACE("hnf_calc", tout << "is_correct_form() does not hold" << std::endl;);
            return false;
        }
        return true;
    }
public:
    const M& H() const { return m_H;}
    const M& U() const { return m_U;}
    const M& U_reverse() const { return m_U_reverse; }
private:
#endif
    void copy_buffer_to_col_i_W_modulo() {
        for (unsigned k = m_i; k < m_m; k++) {
            m_W[k][m_i] = m_buffer[k];
        }
    }

    void replace_column_j_by_j_minus_u_col_i_W(unsigned j, const mpq & u) {
        lp_assert(j < m_i);
        for (unsigned k = m_i; k < m_m; k++) {
            m_W[k][j] -= u * m_W[k][m_i];
            //  m_W[k][j] = mod_R_balanced(m_W[k][j]);
        }
    }    

    bool is_unit_matrix(const M& u) const {
        unsigned m = u.row_count();
        unsigned n = u.column_count();
        if (m != n) return false;
        for (unsigned i = 0; i < m; i ++)
            for (unsigned j = 0; j < n; j++) {
                if (i == j) {
                    if (one_of_type<mpq>() != u[i][j])
                        return false;
                } else {
                    if (!is_zero(u[i][j]))
                        return false;
                }
            }
        return true;
    }
    

    // follows Algorithm 2.4.8 of Henri Cohen's "A course on computational algebraic number theory",
    // with some changes related to that we create a low triangle matrix
    // with non-positive elements under the diagonal
    void process_column_in_row_modulo() {
        const mpq& aii = m_W[m_i][m_i];
        const mpq& aij = m_W[m_i][m_j];
        mpq d, p,q;
        hnf_calc::extended_gcd_minimal_uv(aii, aij, d, p, q);
        if (is_zero(d))
            return;
        mpq aii_over_d = mod_R(aii / d);
        mpq aij_over_d = mod_R(aij / d);
        buffer_p_col_i_plus_q_col_j_W_modulo(p, q);
        pivot_column_i_to_column_j_W_modulo(- aij_over_d, aii_over_d);
        copy_buffer_to_col_i_W_modulo();
    }

    void fix_row_under_diagonal_W_modulo() {
        mpq d, u, v;
        if (is_zero(m_W[m_i][m_i])) {
            m_W[m_i][m_i] = m_R;
            u = one_of_type<mpq>();
            d = m_R;
        } else {
            hnf_calc::extended_gcd_minimal_uv(m_W[m_i][m_i], m_R, d, u, v);
        }
        auto & mii = m_W[m_i][m_i];
        mii *= u;
        mii = mod_R(mii);
        if (is_zero(mii))
            mii = d;

        lp_assert(is_pos(mii));

         // adjust column m_i
        for (unsigned k = m_i + 1; k < m_m; k++) {
            m_W[k][m_i] *= u;
            m_W[k][m_i] = mod_R_balanced(m_W[k][m_i]);
        }

        lp_assert(is_pos(mii));
        for (unsigned j = 0; j < m_i; j++) {
            const mpq & mij = m_W[m_i][j];
            if (!is_pos(mij) && - mij < mii)
                continue;
            mpq q = ceil(mij / mii);
            replace_column_j_by_j_minus_u_col_i_W(j, q);
        }
    }

    
    void process_row_modulo() {
        for (m_j = m_i + 1; m_j < m_n; m_j++) {
            process_column_in_row_modulo();
        }
        fix_row_under_diagonal_W_modulo();
    }
    
    void calculate_by_modulo() {
        for (m_i = 0; m_i < m_m; m_i ++) {
            process_row_modulo();
            lp_assert(is_pos(m_W[m_i][m_i]));
            m_R /= m_W[m_i][m_i];
            lp_assert(is_integer(m_R));
            m_half_R = floor(m_R / 2);
        }
    }
    
public:
    hnf(M & A, const mpq & d) :
#ifdef Z3DEBUG
        m_H(A),
        m_A_orig(A),
#endif
        m_W(A),
        m_buffer(std::max(A.row_count(), A.column_count())),
        m_m(A.row_count()),
        m_n(A.column_count()),
        m_d(d),
        m_R(m_d),
        m_half_R(floor(m_R / 2))
    {
        if (m_m == 0 || m_n == 0 || is_zero(m_d))
            return;
#ifdef Z3DEBUG
        prepare_U_and_U_reverse();
        calculate();
        CASSERT("hnf_test", is_correct_final());
#endif
        calculate_by_modulo();
#ifdef Z3DEBUG
        CTRACE("hnf_calc", m_H != m_W,
               tout << "A = "; m_A_orig.print(tout, 4); tout << std::endl;
               tout << "H = "; m_H.print(tout, 4);  tout << std::endl;
               tout << "W = "; m_W.print(tout, 4);  tout << std::endl;);
        lp_assert (m_H == m_W);
#endif
    }

    const M & W() const { return m_W; }
    
};

}
