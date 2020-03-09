/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>
    for matrix B we have
    t0*...*tn-1*B = Q*U*R
    here ti are matrices corresponding to pivot operations,
    including columns and rows swaps,
    or a multiplication matrix row by a number
    Q, R - permutations and U is an upper triangular matrix
Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once

#include "util/vector.h"
#include "util/debug.h"
#include <algorithm>
#include <set>
#include "math/lp/square_sparse_matrix.h"
#include "math/lp/static_matrix.h"
#include <string>
#include "math/lp/numeric_pair.h"
#include <iostream>
#include <fstream>
#include "math/lp/row_eta_matrix.h"
#include "math/lp/square_dense_submatrix.h"
#include "math/lp/dense_matrix.h"
namespace lp {
template <typename T, typename X> // print the nr x nc submatrix at the top left corner
void print_submatrix(square_sparse_matrix<T, X> & m, unsigned mr, unsigned nc);

template <typename M>
void print_matrix(M &m, std::ostream & out);

template <typename T, typename X>
X dot_product(const vector<T> & a, const vector<X> & b) {
    lp_assert(a.size() == b.size());
    auto r = zero_of_type<X>();
    for (unsigned i = 0; i < a.size(); i++) {
        r += a[i] * b[i];
    }
    return r;
}


template <typename T, typename X>
class one_elem_on_diag: public tail_matrix<T, X> {
    unsigned m_i;
    T m_val;
public:
    one_elem_on_diag(unsigned i, T val) : m_i(i), m_val(val) {
#ifdef Z3DEBUG
        m_one_over_val = numeric_traits<T>::one() / m_val;
#endif
    }

    bool is_dense() const override { return false; }

    one_elem_on_diag(const one_elem_on_diag & o);

#ifdef Z3DEBUG
    unsigned m_m;
    unsigned m_n;
    void set_number_of_rows(unsigned m) override { m_m = m; m_n = m; }
    void set_number_of_columns(unsigned n) override { m_m = n; m_n = n; }
    T m_one_over_val;

    T get_elem (unsigned i, unsigned j) const override;

    unsigned row_count() const override { return m_m; } // not defined }
    unsigned column_count() const override { return m_m; } // not defined  }
#endif
    void apply_from_left(vector<X> & w, lp_settings &) override {
        w[m_i] /= m_val;
    }

    void apply_from_right(vector<T> & w) override {
        w[m_i] /= m_val;
    }

    void apply_from_right(indexed_vector<T> & w) override {
        if (is_zero(w.m_data[m_i]))
            return;
        auto & v = w.m_data[m_i] /= m_val;
        if (lp_settings::is_eps_small_general(v, 1e-14)) {
            w.erase_from_index(m_i);
            v = zero_of_type<T>();
        }
    }

    
    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) override;

    void conjugate_by_permutation(permutation_matrix<T, X> & p) {
        // this = p * this * p(-1)
#ifdef Z3DEBUG
        // auto rev = p.get_reverse();
        // auto deb = ((*this) * rev);
        // deb = p * deb;
#endif
        m_i = p.apply_reverse(m_i);

#ifdef Z3DEBUG
        // lp_assert(*this == deb);
#endif
    }
}; // end of one_elem_on_diag

enum class LU_status { OK, Degenerated};

// This class supports updates of the columns of B, and solves systems Bx=b,and yB=c
// Using Suhl-Suhl method described in the dissertation of Achim Koberstein, Chapter 5
template <typename M>
class lu {
    LU_status m_status;
public:
    typedef typename M::coefftype T;
    typedef typename M::argtype   X;
    
    // the fields
    unsigned                   m_dim;
    const M &                  m_A;
    permutation_matrix<T, X>   m_Q;
    permutation_matrix<T, X>   m_R;
    permutation_matrix<T, X>   m_r_wave;
    square_sparse_matrix<T, X>        m_U;
    square_dense_submatrix<T, X>* m_dense_LU;
    
    vector<tail_matrix<T, X> *> m_tail;
    lp_settings &               m_settings;
    bool                        m_failure;
    indexed_vector<T>           m_row_eta_work_vector;
    indexed_vector<T>           m_w_for_extension;
    indexed_vector<T>           m_y_copy;
    indexed_vector<unsigned>    m_ii; //to optimize the work with the m_index fields
    unsigned                    m_refactor_counter;
    // constructor
    // if A is an m by n matrix then basis has length m and values in [0,n); the values are all different
    // they represent the set of m columns
    lu(const M & A,
       vector<unsigned>& basis,
       lp_settings & settings);
    lu(const M & A, lp_settings&);
    void debug_test_of_basis(const M & A, vector<unsigned> & basis);
    void solve_Bd_when_w_is_ready(vector<T> & d, indexed_vector<T>& w );
    void solve_By(indexed_vector<X> & y);

    void solve_By(vector<X> & y);

    void solve_By_for_T_indexed_only(indexed_vector<T>& y, const lp_settings &);

    template <typename L>
    void solve_By_when_y_is_ready(indexed_vector<L> & y);
    void solve_By_when_y_is_ready_for_X(vector<X> & y);
    void solve_By_when_y_is_ready_for_T(vector<T> & y, vector<unsigned> & index);
    void print_indexed_vector(indexed_vector<T> & w, std::ofstream & f);

    void print_matrix_compact(std::ostream & f);

    void print(indexed_vector<T> & w, const vector<unsigned>& basis);
    void solve_Bd(unsigned a_column, vector<T> & d, indexed_vector<T> & w);
    void solve_Bd(unsigned a_column, indexed_vector<T> & d, indexed_vector<T> & w);
    void solve_Bd_faster(unsigned a_column, indexed_vector<T> & d); // d is the right side on the input and the solution at the exit

    void  solve_yB(vector<T>& y);

    void  solve_yB_indexed(indexed_vector<T>& y);

    void add_delta_to_solution_indexed(indexed_vector<T>& y);

    void add_delta_to_solution(const vector<T>& yc, vector<T>& y);

    
    void find_error_of_yB(vector<T>& yc, const vector<T>& y,
                          const vector<unsigned>& basis);

    void find_error_of_yB_indexed(const indexed_vector<T>& y,
                                  const vector<int>& heading, const lp_settings& settings);

    
    void solve_yB_with_error_check(vector<T> & y, const vector<unsigned>& basis);

    void solve_yB_with_error_check_indexed(indexed_vector<T> & y, const vector<int>& heading, const vector<unsigned> & basis, const lp_settings &);

    void apply_Q_R_to_U(permutation_matrix<T, X> & r_wave);


    LU_status get_status() { return m_status; }

    void set_status(LU_status status) {
        m_status = status;
    }

    ~lu();

    void init_vector_y(vector<X> & y);

    void perform_transformations_on_w(indexed_vector<T>& w);

    void init_vector_w(unsigned entering, indexed_vector<T> & w);
    void apply_lp_list_to_w(indexed_vector<T> & w);
    void apply_lp_list_to_y(vector<X>& y);

    void swap_rows(int j, int k);

    void swap_columns(int j, int pivot_column);

    void push_matrix_to_tail(tail_matrix<T, X>* tm) {
        m_tail.push_back(tm);
    }

    bool pivot_the_row(int row);

    eta_matrix<T, X> * get_eta_matrix_for_pivot(unsigned j);
    // we're processing the column j now
    eta_matrix<T, X> * get_eta_matrix_for_pivot(unsigned j, square_sparse_matrix<T, X>& copy_of_U);

    // see page 407 of Chvatal
    unsigned transform_U_to_V_by_replacing_column(indexed_vector<T> & w, unsigned leaving_column_of_U);

#ifdef Z3DEBUG
    void check_vector_w(unsigned entering);

    void check_apply_matrix_to_vector(matrix<T, X> *lp, T *w);

    void check_apply_lp_lists_to_w(T * w);

    // provide some access operators for testing
    permutation_matrix<T, X> & Q() { return m_Q; }
    permutation_matrix<T, X> & R() { return m_R; }
    matrix<T, X> & U() { return m_U; }
    unsigned tail_size() { return m_tail.size(); }

    tail_matrix<T, X> * get_lp_matrix(unsigned i) {
        return m_tail[i];
    }

    T B_(unsigned i, unsigned j,  const vector<unsigned>& basis) {
        return m_A[i][basis[j]];
    }

    unsigned dimension() { return m_dim; }

#endif


    unsigned get_number_of_nonzeroes() {
        return m_U.get_number_of_nonzeroes();
    }


    void process_column(int j);

    bool is_correct(const vector<unsigned>& basis);
    bool is_correct();


#ifdef Z3DEBUG
    dense_matrix<T, X> tail_product();
    dense_matrix<T, X>  get_left_side(const vector<unsigned>& basis);
    dense_matrix<T, X>  get_left_side();

    dense_matrix<T, X>  get_right_side();
#endif

    // needed for debugging purposes
    void copy_w(T *buffer, indexed_vector<T> & w);

    // needed for debugging purposes
    void restore_w(T *buffer, indexed_vector<T> & w);
    bool all_columns_and_rows_are_active();

    bool too_dense(unsigned j) const;

    void pivot_in_dense_mode(unsigned i);

    void create_initial_factorization();

    void calculate_r_wave_and_update_U(unsigned bump_start, unsigned bump_end, permutation_matrix<T, X> & r_wave);

    void scan_last_row_to_work_vector(unsigned lowest_row_of_the_bump);

    bool diagonal_element_is_off(T /* diag_element */) { return false; }

    void pivot_and_solve_the_system(unsigned replaced_column, unsigned lowest_row_of_the_bump);
    // see Achim Koberstein's thesis page 58, but here we solve the system and pivot to the last
    // row at the same time
    row_eta_matrix<T, X> *get_row_eta_matrix_and_set_row_vector(unsigned replaced_column, unsigned lowest_row_of_the_bump, const T &  pivot_elem_for_checking);

    void replace_column(T pivot_elem, indexed_vector<T> & w, unsigned leaving_column_of_U);

    void calculate_Lwave_Pwave_for_bump(unsigned replaced_column, unsigned lowest_row_of_the_bump);

    void calculate_Lwave_Pwave_for_last_row(unsigned lowest_row_of_the_bump, T diagonal_element);

    void prepare_entering(unsigned entering, indexed_vector<T> & w) {
        init_vector_w(entering, w);
    }
    bool need_to_refactor() { return m_refactor_counter >= 200; }
    
    void adjust_dimension_with_matrix_A() {
        lp_assert(m_A.row_count() >= m_dim);
        m_dim = m_A.row_count();
        m_U.resize(m_dim);
        m_Q.resize(m_dim);
        m_R.resize(m_dim);
        m_row_eta_work_vector.resize(m_dim);
    }


    std::unordered_set<unsigned> get_set_of_columns_to_replace_for_add_last_rows(const vector<int> & heading) const {
        std::unordered_set<unsigned> columns_to_replace;
        unsigned m = m_A.row_count();
        unsigned m_prev = m_U.dimension();

        lp_assert(m_A.column_count() == heading.size());

        for (unsigned i = m_prev; i < m; i++) {
            for (const row_cell<T> & c : m_A.m_rows[i]) {
                int h = heading[c.var()];
                if (h < 0) {
                    continue;
                }
                columns_to_replace.insert(c.var());
            }
        }
        return columns_to_replace;
    }
    
    void add_last_rows_to_B(const vector<int> & heading, const std::unordered_set<unsigned> & columns_to_replace) {
        unsigned m = m_A.row_count();
        lp_assert(m_A.column_count() == heading.size());
        adjust_dimension_with_matrix_A();
        m_w_for_extension.resize(m);
        // At this moment the LU is correct      
        // for B extended by only by ones at the diagonal in the lower right corner

        for (unsigned j :columns_to_replace) {
            lp_assert(heading[j] >= 0);
            replace_column_with_only_change_at_last_rows(j, heading[j]);
            if (get_status() == LU_status::Degenerated)
                break;
        }
    }
    // column j is a basis column, and there is a change in the last rows
    void replace_column_with_only_change_at_last_rows(unsigned j, unsigned column_to_change_in_U) {
        init_vector_w(j, m_w_for_extension);
        replace_column(zero_of_type<T>(), m_w_for_extension, column_to_change_in_U);
    }

    bool has_dense_submatrix() const {
        for (auto m : m_tail)
            if (m->is_dense())
                return true;
        return false;
    }
    
}; // end of lu

template <typename M>
void init_factorization(lu<M>* & factorization, M & m_A, vector<unsigned> & m_basis, lp_settings &m_settings);

#ifdef Z3DEBUG
template <typename T, typename X, typename M>
dense_matrix<T, X>  get_B(lu<M>& f, const vector<unsigned>& basis);

template <typename T, typename X, typename M>
dense_matrix<T, X>  get_B(lu<M>& f);
#endif
}
