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
    vector<bool>               m_terms_upper;
    svector<constraint_index>  m_constraints_for_explanation;
    vector<mpq>                m_right_sides;
    lp_settings &              m_settings;
    mpq                        m_abs_max;
    bool                       m_overflow;
public:

    const mpq & abs_max() const { return m_abs_max; }
    
    hnf_cutter(lp_settings & settings) : m_settings(settings),
                                         m_abs_max(zero_of_type<mpq>()) {}

    unsigned terms_count() const {
        return m_terms.size();
    }

    const vector<const lar_term*>& terms() const { return m_terms; }
    const svector<unsigned>& constraints_for_explanation() const {
        return m_constraints_for_explanation;
    }
    const vector<mpq> & right_sides() const { return m_right_sides; }
    void clear() {
        // m_A will be filled from scratch in init_matrix_A
        m_var_register.clear();
        m_terms.clear();
        m_terms_upper.clear();
        m_constraints_for_explanation.clear();
        m_right_sides.clear();
        m_abs_max = zero_of_type<mpq>();
        m_overflow = false;
    }
    void add_term(const lar_term* t, const mpq &rs, constraint_index ci, bool upper_bound) {
        m_terms.push_back(t);
        m_terms_upper.push_back(upper_bound);
        if (upper_bound)
            m_right_sides.push_back(rs);
        else
            m_right_sides.push_back(-rs);
        
        m_constraints_for_explanation.push_back(ci);
       
        for (const auto &p : *t) {
            m_var_register.add_var(p.var());
            mpq t = abs(ceil(p.coeff()));
            if (t > m_abs_max)
                m_abs_max = t;
        }
    }
    
    void print(std::ostream & out) {
        out << "terms = " << m_terms.size() << ", var = " << m_var_register.size() << std::endl;
    }

    void initialize_row(unsigned i) {
        mpq sign = m_terms_upper[i]? one_of_type<mpq>(): - one_of_type<mpq>();
        m_A.init_row_from_container(i, * m_terms[i], [this](unsigned j) { return m_var_register.add_var(j);}, sign);
    }

    void init_matrix_A() {
        m_A = general_matrix(terms_count(), vars().size());
        for (unsigned i = 0; i < terms_count(); i++)
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
        for (unsigned i : basis_rows) {
            b.push_back(m_right_sides[i]);
        }
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

        // // test region
        // vector<mpq> ei(H.row_count(), zero_of_type<mpq>());
        // ei[i] = one_of_type<mpq>();
        // vector<mpq> pr = row * H;
        // pr.shrink(ei.size());
        // lp_assert(ei == pr);
        // // end test region
        
    }

    void fill_term(const vector<mpq> & row, lar_term& t) {
        for (unsigned j = 0; j < row.size(); j++) {
            if (!is_zero(row[j]))
                t.add_monomial(row[j], m_var_register.local_to_external(j));
        }
    }
#ifdef Z3DEBUG
    vector<mpq> transform_to_local_columns(const vector<impq> & x) const {
        vector<mpq> ret;
        for (unsigned j = 0; j < vars().size(); j++) {
             ret.push_back(x[m_var_register.local_to_external(j)].x);
        }
        return ret;
    }
#endif
    void shrink_explanation(const svector<unsigned>& basis_rows) {
        svector<unsigned> new_expl;
        for (unsigned i : basis_rows) {
            new_expl.push_back(m_constraints_for_explanation[i]);
        }
        m_constraints_for_explanation = new_expl;
    }

    bool overflow() const { return m_overflow; }
    
    lia_move create_cut(lar_term& t, mpq& k, explanation& ex, bool & upper, const vector<mpq> & x0) {
        // we suppose that x0 has at least one non integer element 
        (void)x0;

        init_matrix_A();
        svector<unsigned> basis_rows;
        mpq big_number = m_abs_max.expt(3);
        mpq d = hnf_calc::determinant_of_rectangular_matrix(m_A, basis_rows, big_number);
        
        // std::cout << "max = " << m_abs_max << ", d = " << d << ", d/max = " << ceil (d /m_abs_max) << std::endl;
        // std::cout << "max cube " << m_abs_max * m_abs_max * m_abs_max << std::endl;

        if (d >= big_number) {
            return lia_move::undef;
        }
        
        if (m_settings.get_cancel_flag()) {
            return lia_move::undef;
        }

        if (basis_rows.size() < m_A.row_count()) {
            m_A.shrink_to_rank(basis_rows);
            shrink_explanation(basis_rows);
        }
        
        hnf<general_matrix> h(m_A, d);        
        vector<mpq> b = create_b(basis_rows);
        lp_assert(m_A * x0 == b);
        find_h_minus_1_b(h.W(), b);
        int cut_row = find_cut_row_index(b);

        if (cut_row == -1) {
            return lia_move::undef;
        }

        // the matrix is not square - we can get
        // all integers in b's projection
        
        vector<mpq> row(m_A.column_count());
        get_ei_H_minus_1(cut_row, h.W(), row);
        vector<mpq> f = row * m_A;
        fill_term(f, t);
        k = floor(b[cut_row]);
        upper = true;
        return lia_move::cut;
    }

    svector<unsigned> vars() const { return m_var_register.vars(); }
};
}
