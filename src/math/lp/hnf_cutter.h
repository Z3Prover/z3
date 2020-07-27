/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    hnf_cutter.h

Abstract:

    Cuts (branches) from Hermite matrices
    The implementation is based on ideas from
    "Cutting the Mix" by Jurgen Christ and Jochen Hoenicke.
Author:
    Lev Nachmanson (levnach)

--*/

#pragma once
#include "math/lp/lar_term.h"
#include "math/lp/hnf.h"
#include "math/lp/general_matrix.h"
#include "math/lp/var_register.h"
#include "math/lp/lia_move.h"
#include "math/lp/explanation.h"

namespace lp  {
class int_solver;
class lar_solver;

class hnf_cutter {
    int_solver&                lia;
    lar_solver&                lra;
    lp_settings &              m_settings;
    general_matrix             m_A;
    vector<const lar_term*>    m_terms;
    vector<bool>               m_terms_upper;
    svector<constraint_index>  m_constraints_for_explanation;
    vector<mpq>                m_right_sides;
    mpq                        m_abs_max;
    bool                       m_overflow;
    var_register               m_var_register;

public:

    
    hnf_cutter(int_solver& lia);

    lia_move make_hnf_cut();

private:
    bool init_terms_for_hnf_cut();
    bool hnf_has_var_with_non_integral_value() const;
    void try_add_term_to_A_for_hnf(tv const& i);

    unsigned terms_count() const { return m_terms.size();  }
    const mpq & abs_max() const { return m_abs_max; }
    const vector<const lar_term*>& terms() const { return m_terms; }
    const svector<unsigned>& constraints_for_explanation() const { return m_constraints_for_explanation; }
    const vector<mpq> & right_sides() const { return m_right_sides; }

    bool is_full() const;

    void clear();
    void add_term(const lar_term* t, const mpq &rs, constraint_index ci, bool upper_bound);
    
    void print(std::ostream & out);

    void initialize_row(unsigned i);
    void init_matrix_A();
    void find_h_minus_1_b(const general_matrix& H, vector<mpq> & b);

    vector<mpq> create_b(const svector<unsigned> & basis_rows);

    int find_cut_row_index(const vector<mpq> & b);

    // fills e_i*H_minus_1
    void get_ei_H_minus_1(unsigned i, const general_matrix& H, vector<mpq> & row);

    void fill_term(const vector<mpq> & row, lar_term& t);
#ifdef Z3DEBUG
    vector<mpq> transform_to_local_columns(const vector<impq> & x) const;
#endif
    void shrink_explanation(const svector<unsigned>& basis_rows);
    bool overflow() const;    
    lia_move create_cut(lar_term& t, mpq& k, explanation* ex, bool & upper
#ifdef Z3DEBUG
                        , const vector<mpq> & x0
#endif
                        );
    svector<unsigned> vars() const;
};
}
