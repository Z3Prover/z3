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
namespace lp {
struct general_matrix {
    typedef mpq coefftype;
    typedef mpq argtype;
    vector<vector<mpq>> m_data;
    unsigned row_count() const { return m_data.size(); }
    unsigned column_count() const { return m_data[0].size(); }
    
    const vector<mpq>& operator[](unsigned i) const { return m_data[i]; }
    vector<mpq>& operator[](unsigned i) { return m_data[i]; }
    void print(std::ostream & out, unsigned blanks = 0) const {
        print_matrix<mpq>(m_data, out, blanks);
    }

    void print_submatrix(std::ostream & out, unsigned k, unsigned blanks = 0) const {
        general_matrix m(row_count() - k, column_count() - k);
        for (unsigned i = k; i < row_count(); i++) {
            for (unsigned j = k; j < column_count(); j++)
                m[i-k][j-k] = (*this)[i][j];
        }
        print_matrix<mpq>(m.m_data, out, blanks);
    }

    
    void copy_column_to_indexed_vector(unsigned entering, indexed_vector<mpq> &w ) const {
        lp_assert(false); //
    }
    general_matrix operator*(const general_matrix & m) const {
        lp_assert(m.row_count() == column_count());
        general_matrix ret;
        auto & v = ret.m_data;
        for (unsigned i = 0; i < row_count(); i ++) {
            v.push_back(vector<mpq>());
            v.back().resize(m.column_count());
            const auto & row = m_data[i];
            for (unsigned j = 0; j < m.column_count(); j++) {
                mpq a(0);
                for (unsigned k = 0; k < column_count(); k++)
                    a += row[k]*m[k][j];
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
        for (unsigned j = 0; j < column_count(); j++) {
            auto t = (*this)[i][j];
            (*this)[i][j] = (*this)[l][j];
            (*this)[l][j] = t; 
        }
    }
    
    void transpose_columns(unsigned j, unsigned k) {
        lp_assert(j != k);
        for (unsigned i = 0; i < row_count(); i++) {
            auto t = (*this)[i][j];
            (*this)[i][j] = (*this)[i][k];
            (*this)[i][k] = t; 
        }
    }
    
    general_matrix(){}
    general_matrix(unsigned n) :m_data(n) {
        for (auto& v : m_data){
            v.resize(n);
        }
    }

    general_matrix(unsigned m, unsigned n) :m_data(m) {
        for (auto& v : m_data){
            v.resize(n);
        }
    }
};
}
