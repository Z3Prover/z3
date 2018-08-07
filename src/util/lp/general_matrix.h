/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include <functional>
namespace lp {
class general_matrix {
    // fields
    permutation_matrix<mpq, mpq>          m_row_permutation;
    permutation_matrix<mpq, mpq>          m_column_permutation;
    vector<vector<mpq>>                   m_data;

public:
    unsigned adjust_row(unsigned row) const{
        return m_row_permutation[row];
    }

    void push_row(vector<mpq> & v) {
        m_data.push_back(v);
        m_row_permutation.resize(m_data.size());
        m_column_permutation.resize(v.size());
    }
    
    unsigned adjust_column(unsigned  col) const{
        return m_column_permutation.apply_reverse(col);
    }

    unsigned adjust_row_inverse(unsigned row) const{
        return m_row_permutation.apply_reverse(row);
    }

    unsigned adjust_column_inverse(unsigned col) const{
        return m_column_permutation[col];
    }

    
    unsigned row_count() const { return m_data.size(); }
    unsigned column_count() const { return m_data.size() > 0? m_data[0].size() : 0; }

    class ref_row {
        general_matrix& m_matrix;
        vector<mpq>& m_row_data;
    public:
        ref_row(general_matrix& m, vector<mpq>& row_data) : m_matrix(m), m_row_data(row_data) {}
        mpq & operator[](unsigned col) { return m_row_data[m_matrix.adjust_column(col)]; }
    };
    class ref_row_const {
        const general_matrix& m_matrix;
        const vector<mpq>& m_row_data;
    public:
        ref_row_const(const general_matrix& m, const vector<mpq>& row_data) : m_matrix(m), m_row_data(row_data) {}
        const mpq&  operator[](unsigned col) const { return m_row_data[m_matrix.adjust_column(col)]; }
    };
    
    ref_row operator[](unsigned i) { return ref_row(*this, m_data[adjust_row(i)]); }
    ref_row_const operator[](unsigned i) const { return ref_row_const(*this, m_data[adjust_row(i)]); }

    void print(std::ostream & out, unsigned blanks = 0) const {
        unsigned m = row_count();
        unsigned n = column_count();
        general_matrix g(m, n);
        for (unsigned i = 0; i < m; i++)
            for (unsigned j = 0; j < n; j++)
                g[i][j] = (*this)[i][j];
        print_matrix<mpq>(g.m_data, out, blanks);
    }
    void print(std::ostream & out, const char * ss) const {
        std::string s(ss);
        out << s;
        print(out, static_cast<unsigned>(s.size()));
    }

    void print_submatrix(std::ostream & out, unsigned k, unsigned blanks = 0) const {
        general_matrix m(row_count() - k, column_count() - k);
        for (unsigned i = k; i < row_count(); i++) {
            for (unsigned j = k; j < column_count(); j++)
                m[i-k][j-k] = (*this)[i][j];
        }
        print_matrix<mpq>(m.m_data, out, blanks);
    }

    void clear() { m_data.clear(); }

    bool row_is_initialized_correctly(const vector<mpq>& row) {
        lp_assert(row.size() == column_count());
        for (unsigned j = 0; j < row.size(); j ++)
            lp_assert(is_zero(row[j]));
        return true;
    }
    
    template <typename T>
    void init_row_from_container(int i, const T & c, std::function<unsigned (unsigned)> column_fix, const mpq& sign) {
        auto & row = m_data[adjust_row(i)];
        lp_assert(row_is_initialized_correctly(row));
        for (const auto & p : c) {
            unsigned j = adjust_column(column_fix(p.var()));
            row[j] = sign * p.coeff();
        }
    }
    
    void copy_column_to_indexed_vector(unsigned entering, indexed_vector<mpq> &w ) const {
        lp_assert(false); // not implemented
    }
    general_matrix operator*(const general_matrix & m) const {
        lp_assert(m.row_count() == column_count());
        general_matrix ret(row_count(), m.column_count());
        for (unsigned i = 0; i < row_count(); i ++) {
             for (unsigned j = 0; j < m.column_count(); j++) {
                mpq a(0);
                for (unsigned k = 0; k < column_count(); k++)
                    a += ((*this)[i][k])*m[k][j];
                ret[i][j] = a;
            }
        }
        return ret;
    }

    bool elements_are_equal(const general_matrix& m) const {
        for (unsigned i = 0; i < row_count(); i++)
            for (unsigned j = 0; j < column_count(); j++)
                if ( (*this)[i][j] != m[i][j])
                    return false;
        return true;
    }

    bool elements_are_equal_modulo(const general_matrix& m, const mpq & d) const {
        for (unsigned i = 0; i < row_count(); i++)
            for (unsigned j = 0; j < column_count(); j++)
                if (!is_zero(((*this)[i][j] - m[i][j]) % d)) 
                    return false;
        return true;
    }
    bool operator==(const general_matrix& m) const {
        return row_count() == m.row_count() && column_count() == m.column_count() && elements_are_equal(m);
    }

    bool operator!=(const general_matrix& m) const {
        return !(*this == m);
    }

    bool equal_modulo(const general_matrix& m, const mpq & d) const {
        return row_count() == m.row_count() && column_count() == m.column_count() && elements_are_equal_modulo(m, d);
    }

    
    vector<mpq> operator*(const vector<mpq> & x) const {
        vector<mpq> r;
        lp_assert(x.size() == column_count());
        for (unsigned i = 0; i < row_count(); i++) {
            mpq v(0);
            for (unsigned j = 0; j < column_count(); j++) {
                v += (*this)[i][j] * x[j];
            }
            r.push_back(v);
        }
        return r;
    }

    // bool create_upper_triangle(general_matrix& m, vector<mpq>& x) {
    //     for (unsigned i = 1; i < m.row_count(); i++) {
    //         lp_assert(false); // to be continued
    //     }
    // }

    // bool solve_A_x_equal_b(const general_matrix& m, vector<mpq>& x, const vector<mpq>& b) const {
    //     auto m_copy = m;
    //     // for square matrices
    //     lp_assert(row_count() == b.size());
    //     lp_assert(x.size() == column_count());
    //     lp_assert(row_count() == column_count());
    //     x = b;
    //     create_upper_triangle(copy_of_m, x);
    //     solve_on_triangle(copy_of_m, x);
    // }
    //

    void transpose_rows(unsigned i, unsigned l) {
        lp_assert(i != l);
        m_row_permutation.transpose_from_right(i, l);
    }
    
    void transpose_columns(unsigned j, unsigned k) {
        lp_assert(j != k);
        m_column_permutation.transpose_from_left(j, k);
    }
    
    general_matrix(){}
    general_matrix(unsigned n) :
        m_row_permutation(n),
        m_column_permutation(n),
        m_data(n)
    {
        for (auto& v : m_data){
            v.resize(n);
        }
    }
    
    general_matrix(unsigned m, unsigned n) :
        m_row_permutation(m),
        m_column_permutation(n),
        m_data(m) {
        for (auto& v : m_data){
            v.resize(n);
        }
    }

    void shrink_to_rank(const svector<unsigned>& basis_rows) {
        if (basis_rows.size() == row_count()) return;
        vector<vector<mpq>> data; // todo : not efficient code
        for (unsigned i : basis_rows)
            data.push_back(m_data[i]);
        m_data = data;
    }

    // used for debug only
    general_matrix take_first_n_columns(unsigned n) const {
        lp_assert(n <= column_count());
        if (n == column_count())
            return *this;
        general_matrix ret(row_count(), n);
        for (unsigned i = 0; i < row_count(); i++)
            for (unsigned j = 0; j < n; j++)
                ret[i][j] = (*this)[i][j];
        return ret;
    }
    inline
    friend vector<mpq> operator*(const vector<mpq> & f, const general_matrix& a) {
        vector<mpq> r(a.column_count());
        for (unsigned j = 0; j < a.column_count(); j ++) {
            mpq t = zero_of_type<mpq>();
            for (unsigned i = 0; i < a.row_count(); i++) {
                t += f[i] * a[i][j];
            }
            r[j] = t;
        }
        return r;
    }
};

}
