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
#include "util/lp/lar_term.h"
#include "util/lp/hnf.h"
#include "util/lp/general_matrix.h"
#include "util/lp/var_register.h"
#include "util/lp/lia_move.h"
#include "util/lp/explanation.h"

namespace lp  {
class hnf_cutter {
    var_register               m_var_register;
    general_matrix             m_A;
    vector<const lar_term*>    m_terms;
    vector<mpq>                m_right_sides;
    unsigned                   m_row_count;
    unsigned                   m_column_count;
    lp_settings &              m_settings;
public:
    hnf_cutter(lp_settings & settings) : m_row_count(0), m_column_count(0), m_settings(settings) {}

    unsigned row_count() const {
        return m_row_count;
    }

    const vector<const lar_term*>& terms() const { return m_terms; }
    const vector<mpq> & right_sides() const { return m_right_sides; }
    void clear() {
        // m_A will be filled from scratch in init_matrix_A
        m_var_register.clear();
        m_terms.clear();
        m_right_sides.clear();
        m_row_count = m_column_count = 0;
    }
    void add_term(const lar_term* t, const mpq &rs) {
        m_terms.push_back(t);
        for (const auto &p : *t) {
            m_var_register.add_var(p.var());
        }
        m_right_sides.push_back(rs);
        if (m_terms.size() <= m_var_register.size()) { // capture the maximal acceptable sizes
            m_row_count = m_terms.size();
            m_column_count = m_var_register.size();
        }
        
    }
    void print(std::ostream & out) {
        out << "terms = " << m_terms.size() << ", var = " << m_var_register.size() << std::endl;
    }

    void initialize_row(unsigned i) {
        m_A.init_row_from_container(i, * m_terms[i], [this](unsigned j) { return m_var_register.add_var(j);});
    }

    void init_matrix_A() {
        m_A = general_matrix(m_row_count, m_column_count);
        // use the last suitable counts to make the number
        // of rows less than or equal to the number of columns
        for (unsigned i = 0; i < m_row_count; i++)
            initialize_row(i);
    }

    // todo: as we need only one row i with non integral b[i] need to optimize later
    void find_h_minus_1_b(const general_matrix& H, vector<mpq> & b) {
        // the solution will be put into b
        for (unsigned i = 0; i < H.row_count() ;i++) {
            for (unsigned j = 0; j < i; j++) {
                b[i] -= H[i][j]*b[j];
            }
            b[i] /= H[i][i];
            // consider return from here if b[i] is not an integer and return i
        }
    }

    vector<mpq> create_b(const svector<unsigned> & basis_rows) {
        if (basis_rows.size() == m_right_sides.size())
            return m_right_sides;
        vector<mpq> b;
        for (unsigned i : basis_rows)
            b.push_back(m_right_sides[i]);
        return b;
    }

    int find_cut_row_index(const vector<mpq> & b) {
        int ret = -1;
        int n = 0;
        for (int i = 0; i < static_cast<int>(b.size()); i++) {
            if (is_int(b[i])) continue;
            if (n == 0 ) {
                lp_assert(ret == -1);
                n = 1;
                ret = i;
            } else {
                if (m_settings.random_next() % (++n) == 0) {
                    ret = i;
                }
            }
        }
        return ret;
    }


    // fills e_i*H_minus_1
    void get_ei_H_minus_1(unsigned i, const general_matrix& H, vector<mpq> & row) {
        // we solve x = ei * H_min_1
        // or x * H = ei
        unsigned m = H.row_count();
        for (unsigned k = i + 1; k < m; k++) {
            row[k] = zero_of_type<mpq>();
        }
        row[i] = one_of_type<mpq>() / H[i][i];
        for(int k = i - 1; k >= 0; k--) {
            mpq t = zero_of_type<mpq>();
            for (unsigned l = k + 1; l <= i; l++) {
                t += H[l][k]*row[l];
            }
            row[k] = -t / H[k][k]; 
        }

        // test region
        vector<mpq> ei(H.row_count(), zero_of_type<mpq>());
        ei[i] = one_of_type<mpq>();
        vector<mpq> pr = row * H;
        pr.shrink(ei.size());
        lp_assert(ei == pr);
        // end test region
        
    }

    void fill_term(const vector<mpq> & row, lar_term& t) {
        for (unsigned j = 0; j < row.size(); j++) {
            if (!is_zero(row[j]))
                t.add_monomial(row[j], m_var_register.local_var_to_user_var(j));
        }
    }
#ifdef Z3DEBUG
    vector<mpq> transform_to_local_columns(const vector<impq> & x) const {
        vector<mpq> ret;
        lp_assert(m_column_count <= m_var_register.size());
        for (unsigned j = 0; j < m_column_count;j++) {
            lp_assert(is_zero(x[m_var_register.local_var_to_user_var(j)].y));
            ret.push_back(x[m_var_register.local_var_to_user_var(j)].x);
        }
        return ret;
    }
#endif
    lia_move create_cut(lar_term& t, mpq& k, explanation& ex, bool & upper
                        #ifdef Z3DEBUG
                        ,
                        const vector<mpq> & x0
                        #endif
                        ) {
        init_matrix_A();
        svector<unsigned> basis_rows;
        mpq d = hnf_calc::determinant_of_rectangular_matrix(m_A, basis_rows);
        if (m_settings.get_cancel_flag())
            return lia_move::undef;
        if (basis_rows.size() < m_A.row_count())
            m_A.shrink_to_rank(basis_rows);
        
        hnf<general_matrix> h(m_A, d);
        //  general_matrix A_orig = m_A;
        
        vector<mpq> b = create_b(basis_rows);
        lp_assert(m_A * x0 == b);
        // vector<mpq> bcopy = b;
        find_h_minus_1_b(h.W(), b);
        // lp_assert(bcopy == h.W().take_first_n_columns(b.size()) * b);
        int cut_row = find_cut_row_index(b);
        if (cut_row == -1) {
            return lia_move::undef;
        }
        // test region
        /*
        general_matrix U(m_A.column_count());
        vector<mpq> rt(m_A.column_count());
        for (unsigned i = 0; i < U.row_count(); i++) {
            get_ei_H_minus_1(i, h.W(), rt);
            vector<mpq> ft = rt * A_orig;
            for (unsigned j = 0; j < ft.size(); j++)
                U[i][j] = ft[j];
        }
        std::cout << "U reverse = "; U.print(std::cout, 12); std::cout << std::endl;
        */
        // end test region
        
        vector<mpq> row(m_A.column_count());
        get_ei_H_minus_1(cut_row, h.W(), row);
        vector<mpq> f = row * m_A;
        fill_term(f, t);
        k = floor(b[cut_row]);
        upper = true;
        return lia_move::cut;
    }
};
}
