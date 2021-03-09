/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    hnf_cutter.cpp

Author:
    Lev Nachmanson (levnach)

--*/
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/hnf_cutter.h"

namespace lp  {

    hnf_cutter::hnf_cutter(int_solver& lia): 
        lia(lia), 
        lra(lia.lra),
        m_settings(lia.settings()),
        m_abs_max(zero_of_type<mpq>()),
        m_var_register(0) {}
    
    bool hnf_cutter::is_full() const {
        return
            terms_count() >= lia.settings().limit_on_rows_for_hnf_cutter ||
            vars().size() >= lia.settings().limit_on_columns_for_hnf_cutter;
    }

    void hnf_cutter::clear() {
        // m_A will be filled from scratch in init_matrix_A
        m_var_register.clear();
        m_terms.clear();
        m_terms_upper.clear();
        m_constraints_for_explanation.clear();
        m_right_sides.clear();
        m_abs_max = zero_of_type<mpq>();
        m_overflow = false;
    }

    void hnf_cutter::add_term(const lar_term* t, const mpq &rs, constraint_index ci, bool upper_bound) {
        m_terms.push_back(t);
        m_terms_upper.push_back(upper_bound);
        if (upper_bound)
            m_right_sides.push_back(rs);
        else
            m_right_sides.push_back(-rs);
        
        m_constraints_for_explanation.push_back(ci);
       
        for (lar_term::ival p : *t) {
            m_var_register.add_var(p.column().index(), true); // hnf only deals with integral variables for now
            mpq t = abs(ceil(p.coeff()));
            if (t > m_abs_max)
                m_abs_max = t;
        }
    }
    
    void hnf_cutter::print(std::ostream & out) {
        out << "terms = " << m_terms.size() << ", var = " << m_var_register.size() << std::endl;
    }

    void hnf_cutter::initialize_row(unsigned i) {
        mpq sign = m_terms_upper[i]? one_of_type<mpq>(): - one_of_type<mpq>();
        m_A.init_row_from_container(i, * m_terms[i], [this](unsigned j) { return m_var_register.add_var(j, true);}, sign);// hnf only deals with integral variables for now
    }

    void hnf_cutter::init_matrix_A() {
        m_A = general_matrix(terms_count(), vars().size());
        for (unsigned i = 0; i < terms_count(); i++)
            initialize_row(i);
    }

    // todo: as we need only one row i with non integral b[i] need to optimize later
    void hnf_cutter::find_h_minus_1_b(const general_matrix& H, vector<mpq> & b) {
        // the solution will be put into b
        for (unsigned i = 0; i < H.row_count() ;i++) {
            for (unsigned j = 0; j < i; j++) {
                b[i] -= H[i][j]*b[j];
            }
            b[i] /= H[i][i];
            // consider return from here if b[i] is not an integer and return i
        }
    }

    vector<mpq> hnf_cutter::create_b(const svector<unsigned> & basis_rows) {
        if (basis_rows.size() == m_right_sides.size())
            return m_right_sides;
        vector<mpq> b;
        for (unsigned i : basis_rows) {
            b.push_back(m_right_sides[i]);
        }
        return b;
    }

    int hnf_cutter::find_cut_row_index(const vector<mpq> & b) {
        int ret = -1;
        int n = 0;
        for (int i = 0; i < static_cast<int>(b.size()); i++) {
            if (is_integer(b[i])) continue;
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
    void hnf_cutter::get_ei_H_minus_1(unsigned i, const general_matrix& H, vector<mpq> & row) {
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
    }

    void hnf_cutter::fill_term(const vector<mpq> & row, lar_term& t) {
        for (unsigned j = 0; j < row.size(); j++) {
            if (!is_zero(row[j]))
                t.add_monomial(row[j], m_var_register.local_to_external(j));
        }
    }
#ifdef Z3DEBUG
    vector<mpq> hnf_cutter::transform_to_local_columns(const vector<impq> & x) const {
        vector<mpq> ret;
        for (unsigned j = 0; j < vars().size(); j++) {
             ret.push_back(x[m_var_register.local_to_external(j)].x);
        }
        return ret;
    }
#endif
    void hnf_cutter::shrink_explanation(const svector<unsigned>& basis_rows) {
        svector<unsigned> new_expl;
        for (unsigned i : basis_rows) {
            new_expl.push_back(m_constraints_for_explanation[i]);
        }
        m_constraints_for_explanation = new_expl;
    }

    bool hnf_cutter::overflow() const { return m_overflow; }
/*
  Here is the citation from "Cutting the Mix" by Jürgen Christ and Jochen Hoenicke.

  The algorithm is based on the Simplex algorithm. The solution space
  forms a polyhedron in Q^n . If the solution space is non-empty, the
  Simplex algorithm returns a solution of Ax <= b . We further assume
  that the returned solution x0 is a vertex of the polyhedron, i. e.,
  there is a nonsingular square submatrix A′ and a corresponding
  vector b′ , such that A′x0=b′ . We call A′x <=b′ the defining
  constraints of the vertex. If the returned solution is not on a
  vertex we introduce artificial branches on input variables into A
  and use these branches as defining constraints. These branches are
  rarely needed in practise.

The main idea is to bring the constraint system A′x<=b′ into a Hermite
normal form H and to compute the unimodular matrix U with A′U=H . The
Hermite normal form is uniquely defined. The constraint system A′x<=b′
is equivalent to Hy <=b′ with y:=(U−1)x . Since the solution x0 of
A′x0=b′ is not integral, the corresponding vector y0=(U−1)x0 is not
integral, either. The cuts from proofs algorithm creates an extended
branch on one of the components y_i of y , i. e., y_i <= floor(y0_i) or
y_i>=ceil(y0_i).  Further on in the paper there is a lemma showing that
branch y_i >= ceil(y0_i) is impossible.
 */
    lia_move hnf_cutter::create_cut(lar_term& t, mpq& k, explanation* ex, bool & upper
#ifdef Z3DEBUG
                                    , const vector<mpq> & x0
                                    // we suppose that x0 has at least one non integer element 
#endif                                                                                                            
                                    ) {
        init_matrix_A();
        svector<unsigned> basis_rows;
        mpq big_number = m_abs_max.expt(3);
        mpq d = hnf_calc::determinant_of_rectangular_matrix(m_A, basis_rows, big_number);
        
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
#ifdef Z3DEBUG
        lp_assert(m_A * x0 == b);
#endif

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

    svector<unsigned> hnf_cutter::vars() const { return m_var_register.vars(); }

    void hnf_cutter::try_add_term_to_A_for_hnf(tv const &i) {
        mpq rs;
        const lar_term& t = lra.get_term(i);
        constraint_index ci;
        bool upper_bound;
        if (!is_full() && lra.get_equality_and_right_side_for_term_on_current_x(i, rs, ci, upper_bound)) {
            add_term(&t, rs, ci, upper_bound);
        }
    }

    bool hnf_cutter::hnf_has_var_with_non_integral_value() const {
        for (unsigned j : vars())
            if (!lia.get_value(j).is_int())
                return true;
        return false;
    }

    bool hnf_cutter::init_terms_for_hnf_cut() {
        clear();
        for (unsigned i = 0; i < lra.terms().size() && !is_full(); i++) {
            try_add_term_to_A_for_hnf(tv::term(i));
        }
        return hnf_has_var_with_non_integral_value();
    }

    lia_move hnf_cutter::make_hnf_cut() {
        if (!init_terms_for_hnf_cut()) {
            return lia_move::undef;
        }
        lia.settings().stats().m_hnf_cutter_calls++;
        TRACE("hnf_cut", tout << "settings().stats().m_hnf_cutter_calls = " << lia.settings().stats().m_hnf_cutter_calls << "\n";
              for (unsigned i : constraints_for_explanation()) {
                  lra.constraints().display(tout, i);
              }              
              tout << lra.constraints();
              );
#ifdef Z3DEBUG
        vector<mpq> x0 = transform_to_local_columns(lra.r_x());
#endif
        lia_move r =  create_cut(lia.m_t, lia.m_k, lia.m_ex, lia.m_upper
#ifdef Z3DEBUG
                                 , x0
#endif
                                 );

        if (r == lia_move::cut) {      
            TRACE("hnf_cut",
                  lra.print_term(lia.m_t, tout << "cut:"); 
                  tout << " <= " << lia.m_k << std::endl;
                  for (unsigned i : constraints_for_explanation()) {
                      lra.constraints().display(tout, i);
                  }              
                  );
            lp_assert(lia.current_solution_is_inf_on_cut());
            lia.settings().stats().m_hnf_cuts++;
            lia.m_ex->clear();        
            for (unsigned i : constraints_for_explanation()) {
                lia.m_ex->push_back(i);
            }
        } 
        return r;
    }

}
