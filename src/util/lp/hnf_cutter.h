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
    var_register m_var_register;
    general_matrix m_A;
    vector<const lar_term*> m_terms;
    vector<mpq> m_rigth_sides;
    unsigned m_row_count;
    unsigned m_column_count;
public:
    void clear() {
        m_var_register.clear();
        m_terms.clear();
    }
    void add_term(const lar_term* t, const mpq &rs) {
        m_terms.push_back(t);
        for (const auto &p : *t) {
            m_var_register.add_var(p.var());
        }
        m_rigth_sides.push_back(rs);
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

    void find_h_minus_1_b() {
    }
    
    lia_move create_cut(lar_term& t, mpq& k, explanation& ex, bool & upper) {
        init_matrix_A();
        svector<unsigned> basis_rows;
        mpq d = hnf_calc::determinant_of_rectangular_matrix(m_A, basis_rows);
        if (basis_rows.size() < m_A.row_count())
            m_A.shrink_to_rank(basis_rows);
        
        hnf<general_matrix> h(m_A, d);
        std::cout << "hnf = "; h.W().print(std::cout, 6);
        find_h_minus_1_b();
        return lia_move::undef;
    }
};
}
