/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

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
    std::function<unsigned ()> m_random_next;
public:
    hnf_cutter(std::function<unsigned()> random) : m_random_next(random) {}

    void clear() {
        m_var_register.clear();
        m_terms.clear();
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
        m_A = general_matrix(m_row_count, m_column_count); // use the last suitable counts to make the number
        // of rows less than or equal to the number of columns
        for (unsigned i = 0; i < m_row_count; i++)
            initialize_row(i);
        std::cout << "m_A = "; m_A.print(std::cout, 6);
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

    int find_cut_row(const vector<mpq> & b) {
        int ret = -1;
        int n = 0;
        for (int i = 0; i < static_cast<int>(b.size()); i++) {
            if (!is_int(b[i])) {
                if (n == 0 ) {
                    lp_assert(ret == -1);
                    n = 1;
                    ret = i;
                } else {
                    if (m_random_next() % (++n) == 0) {
                       ret = i;
                    }
                }
            }
        }
        return ret;
    }
    
    lia_move create_cut(lar_term& t, mpq& k, explanation& ex, bool & upper) {
        init_matrix_A();
        svector<unsigned> basis_rows;
        mpq d = hnf_calc::determinant_of_rectangular_matrix(m_A, basis_rows);
        if (basis_rows.size() < m_A.row_count())
            m_A.shrink_to_rank(basis_rows);
        
        hnf<general_matrix> h(m_A, d);
        std::cout << "hnf = "; h.W().print(std::cout, 6);
        
        vector<mpq> b = create_b(basis_rows);
        vector<mpq> bcopy = b;
        find_h_minus_1_b(h.W(), b);
        
        std::cout << "b = "; print_vector<mpq, vector<mpq>>(b ,std::cout);
        lp_assert(bcopy == h.W().take_first_n_columns(b.size()) * b);
        int cut_row = find_cut_row(b);
        if (cut_row == -1) {
            std::cout << "cut row == -1\n";
            return lia_move::undef;
        }
        return lia_move::undef;
    }
};
}
