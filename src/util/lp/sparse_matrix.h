/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include "util/lp/permutation_matrix.h"
#include <unordered_map>
#include "util/lp/static_matrix.h"
#include <set>
#include <utility>
#include <string>
#include <algorithm>
#include <queue>
#include "util/lp/indexed_value.h"
#include "util/lp/indexed_vector.h"
#include <functional>
#include "util/lp/lp_settings.h"
#include "util/lp/eta_matrix.h"
#include "util/lp/binary_heap_upair_queue.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/int_set.h"
namespace lean {
// it is a square matrix
template <typename T, typename X>
class sparse_matrix
#ifdef LEAN_DEBUG
    : public matrix<T, X>
#endif
{
    struct col_header {
        unsigned m_shortened_markovitz;
        vector<indexed_value<T>> m_values; // the actual column values

        col_header(): m_shortened_markovitz(0) {}

        void shorten_markovich_by_one() {
            m_shortened_markovitz++;
        }

        void zero_shortened_markovitz() {
            m_shortened_markovitz = 0;
        }
    };

    unsigned                          m_n_of_active_elems;
    binary_heap_upair_queue<unsigned> m_pivot_queue;
public:
    vector<vector<indexed_value<T>>>  m_rows;
    vector<col_header>                m_columns;
    permutation_matrix<T, X>          m_row_permutation;
    permutation_matrix<T, X>          m_column_permutation;
    // m_work_pivot_vector[j] = offset of elementh of j-th column in the row we are pivoting to
    // if the column is not present then m_work_pivot_vector[j] is -1
    vector<int>                       m_work_pivot_vector;
    vector<bool>                      m_processed;
    unsigned get_n_of_active_elems() const { return m_n_of_active_elems; }

#ifdef LEAN_DEBUG
    // dense_matrix<T> m_dense;
#endif
    /*
      the rule is: row i is mapped to m_row_permutation[i] and
      column j is mapped to m_column_permutation.apply_reverse(j)
    */

    unsigned adjust_row(unsigned row)  const{
        return m_row_permutation[row];
    }

    unsigned adjust_column(unsigned  col)  const{
        return m_column_permutation.apply_reverse(col);
    }

    unsigned adjust_row_inverse(unsigned row)  const{
        return m_row_permutation.apply_reverse(row);
    }

    unsigned adjust_column_inverse(unsigned  col)  const{
        return m_column_permutation[col];
    }

    void copy_column_from_static_matrix(unsigned col, static_matrix<T, X> const &A, unsigned col_index_in_the_new_matrix);
    void copy_B(static_matrix<T, X> const &A, vector<unsigned> & basis);

public:
    // constructor that copies columns of the basis from A
    sparse_matrix(static_matrix<T, X> const &A, vector<unsigned> & basis);

    class ref_matrix_element {
        sparse_matrix & m_matrix;
        unsigned m_row;
        unsigned m_col;
    public:
        ref_matrix_element(sparse_matrix & m, unsigned row, unsigned col):m_matrix(m), m_row(row), m_col(col) {}
        ref_matrix_element & operator=(T const & v) { m_matrix.set( m_row, m_col, v); return *this; }
        ref_matrix_element & operator=(ref_matrix_element const & v) { m_matrix.set(m_row, m_col, v.m_matrix.get(v.m_row, v.m_col)); return *this; }
        operator T () const { return m_matrix.get(m_row, m_col); }
    };

    class ref_row {
        sparse_matrix & m_matrix;
        unsigned        m_row;
    public:
        ref_row(sparse_matrix & m, unsigned row) : m_matrix(m), m_row(row) {}
        ref_matrix_element operator[](unsigned col) const { return ref_matrix_element(m_matrix, m_row, col); }
    };

    void set_with_no_adjusting_for_row(unsigned row, unsigned col, T val);
    void set_with_no_adjusting_for_col(unsigned row, unsigned col, T val);

    void set_with_no_adjusting(unsigned row, unsigned col, T val);

    void set(unsigned row, unsigned col, T val);

    T const & get_not_adjusted(unsigned row, unsigned col) const;
    T const & get(unsigned row, unsigned col) const;

    ref_row operator[](unsigned row) { return ref_row(*this, row); }

    ref_matrix_element operator()(unsigned row, unsigned col) { return ref_matrix_element(*this, row, col); }

    T operator() (unsigned row, unsigned col) const { return get(row, col); }

    vector<indexed_value<T>> & get_row_values(unsigned row) {
        return m_rows[row];
    }

    vector<indexed_value<T>> const & get_row_values(unsigned row) const {
        return m_rows[row];
    }

    vector<indexed_value<T>> & get_column_values(unsigned col) {
        return m_columns[col].m_values;
    }

    vector<indexed_value<T>> const & get_column_values(unsigned col) const {
        return m_columns[col].m_values;
    }

    // constructor creating a zero matrix of dim*dim
    sparse_matrix(unsigned dim);



    unsigned dimension() const {return static_cast<unsigned>(m_row_permutation.size());}

#ifdef LEAN_DEBUG
    unsigned row_count() const {return dimension();}
    unsigned column_count() const {return dimension();}
#endif

    void init_row_headers();

    void init_column_headers();

    unsigned lowest_row_in_column(unsigned j);

    indexed_value<T> & column_iv_other(indexed_value<T> & iv) {
        return m_rows[iv.m_index][iv.m_other];
    }

    indexed_value<T> & row_iv_other(indexed_value<T> & iv) {
        return m_columns[iv.m_index].m_values[iv.m_other];
    }

    void remove_element(vector<indexed_value<T>> & row_vals, unsigned row_offset, vector<indexed_value<T>> & column_vals, unsigned column_offset);

    void remove_element(vector<indexed_value<T>> & row_chunk, indexed_value<T> & row_el_iv);

    void put_max_index_to_0(vector<indexed_value<T>> & row_vals, unsigned max_index);

    void set_max_in_row(unsigned row) {
        set_max_in_row(m_rows[row]);
    }

    
    void set_max_in_row(vector<indexed_value<T>> & row_vals);

    bool pivot_with_eta(unsigned i, eta_matrix<T, X> *eta_matrix, lp_settings & settings);

    void scan_row_to_work_vector_and_remove_pivot_column(unsigned row, unsigned pivot_column);

    // This method pivots row i to row i0 by muliplying row i by
    // alpha and adding it to row i0.
    // After pivoting the row i0 has a max abs value set correctly at the beginning of m_start,
    // Returns false if the resulting row is all zeroes, and true otherwise
    bool pivot_row_to_row(unsigned i, const T& alpha, unsigned i0, lp_settings & settings );

    // set the max val as well
    // returns false if the resulting row is all zeroes, and true otherwise
    bool set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned i0, indexed_vector<T> & work_vec,
                                                                     lp_settings & settings);


    // set the max val as well
    // returns false if the resulting row is all zeroes, and true otherwise
    bool set_row_from_work_vector_and_clean_work_vector(unsigned i0);

    void remove_zero_elements_and_set_data_on_existing_elements(unsigned row);

    // work_vec here has not adjusted column indices
    void remove_zero_elements_and_set_data_on_existing_elements_not_adjusted(unsigned row, indexed_vector<T> & work_vec, lp_settings & settings);

    void multiply_from_right(permutation_matrix<T, X>& p) {
        //            m_dense = m_dense * p;
        m_column_permutation.multiply_by_permutation_from_right(p);
        //            lean_assert(*this == m_dense);
    }

    void multiply_from_left(permutation_matrix<T, X>& p) {
        //            m_dense = p * m_dense;
        m_row_permutation.multiply_by_permutation_from_left(p);
        //            lean_assert(*this == m_dense);
    }

    void multiply_from_left_with_reverse(permutation_matrix<T, X>& p) {
        //            m_dense = p * m_dense;
        m_row_permutation.multiply_by_permutation_reverse_from_left(p);
        //            lean_assert(*this == m_dense);
    }

    // adding delta columns at the end of the matrix
    void add_columns_at_the_end(unsigned delta);

    void delete_column(int i);

    void swap_columns(unsigned a, unsigned b) {
        // cout << "swaapoiiin" << std::endl;
        // dense_matrix<T, X> d(*this);
        m_column_permutation.transpose_from_left(a, b);
        // d.swap_columns(a, b);
        // lean_assert(*this == d);
    }

    void swap_rows(unsigned a, unsigned b) {
        m_row_permutation.transpose_from_right(a, b);
        //            m_dense.swap_rows(a, b);
        //            lean_assert(*this == m_dense);
    }

    void divide_row_by_constant(unsigned i, const T & t, lp_settings & settings);

    bool close(T a, T b) {
        return // (numeric_traits<T>::precise() && numeric_traits<T>::is_zero(a - b))
            // ||
            fabs(numeric_traits<T>::get_double(a - b)) < 0.0000001;
    }

    // solving x * this = y, and putting the answer into y
    // the matrix here has to be upper triangular
    void solve_y_U(vector<T> & y) const;

    // solving x * this = y, and putting the answer into y
    // the matrix here has to be upper triangular
    void solve_y_U_indexed(indexed_vector<T> & y, const lp_settings &);

    // fills the indices for such that y[i] can be not a zero
    // sort them so the smaller indices come first
    void fill_reachable_indices(std::set<unsigned> & rset, T *y);

    template <typename L>
    void find_error_in_solution_U_y(vector<L>& y_orig, vector<L> & y);

    template <typename L>
    void find_error_in_solution_U_y_indexed(indexed_vector<L>& y_orig, indexed_vector<L> & y,     const vector<unsigned>& sorted_active_rows);

    template <typename L>
    void add_delta_to_solution(const vector<L>& del, vector<L> & y);

    template <typename L>
    void add_delta_to_solution(const indexed_vector<L>& del, indexed_vector<L> & y);

    template <typename L>
    void double_solve_U_y(indexed_vector<L>& y, const lp_settings & settings);

    template <typename L>
    void double_solve_U_y(vector<L>& y);
    // solving this * x = y, and putting the answer into y
    // the matrix here has to be upper triangular
    template <typename L>
    void solve_U_y(vector<L> & y);
    // solving this * x = y, and putting the answer into y
    // the matrix here has to be upper triangular
    template <typename L>
    void solve_U_y_indexed_only(indexed_vector<L> & y, const lp_settings&, vector<unsigned> & sorted_active_rows );

#ifdef LEAN_DEBUG
    T get_elem(unsigned i, unsigned j) const { return get(i, j); }
    unsigned get_number_of_rows() const { return dimension(); }
    unsigned get_number_of_columns() const { return dimension(); }
    virtual void set_number_of_rows(unsigned /*m*/) { }
    virtual void set_number_of_columns(unsigned /*n*/) { }
#endif
    template <typename L>
    L dot_product_with_row (unsigned row, const vector<L> & y) const;

    template <typename L>
    L dot_product_with_row (unsigned row, const indexed_vector<L> & y) const;

    unsigned get_number_of_nonzeroes() const;

    bool get_non_zero_column_in_row(unsigned i, unsigned *j) const;

    void remove_element_that_is_not_in_w(vector<indexed_value<T>> & column_vals, indexed_value<T> & col_el_iv);


    // w contains the new column
    // the old column inside of the matrix has not been changed yet
    void remove_elements_that_are_not_in_w_and_update_common_elements(unsigned column_to_replace, indexed_vector<T> & w);

    void add_new_element(unsigned row, unsigned col, const T& val);

    // w contains the "rest" of the new column; all common elements of w and the old column has been zeroed
    // the old column inside of the matrix has not been changed yet
    void add_new_elements_of_w_and_clear_w(unsigned column_to_replace, indexed_vector<T> & w, lp_settings & settings);

    void replace_column(unsigned column_to_replace, indexed_vector<T> & w, lp_settings &settings);

    unsigned pivot_score(unsigned i, unsigned j);

    void enqueue_domain_into_pivot_queue();

    void set_max_in_rows();

    void zero_shortened_markovitz_numbers();

    void prepare_for_factorization();

    void recover_pivot_queue(vector<upair> & rejected_pivots);

    int elem_is_too_small(unsigned i, unsigned j, int c_partial_pivoting);

    bool remove_row_from_active_pivots_and_shorten_columns(unsigned row);

    void remove_pivot_column(unsigned row);

    void update_active_pivots(unsigned row);

    bool shorten_active_matrix(unsigned row, eta_matrix<T, X> *eta_matrix);

    unsigned pivot_score_without_shortened_counters(unsigned i, unsigned j, unsigned k);
#ifdef LEAN_DEBUG
    bool can_improve_score_for_row(unsigned row, unsigned score, T const & c_partial_pivoting, unsigned k);
    bool really_best_pivot(unsigned i, unsigned j, T const & c_partial_pivoting, unsigned k);
    void print_active_matrix(unsigned k, std::ostream & out);
#endif
    bool pivot_queue_is_correct_for_row(unsigned i, unsigned k);

    bool pivot_queue_is_correct_after_pivoting(int k);

    bool get_pivot_for_column(unsigned &i, unsigned &j, int c_partial_pivoting, unsigned k);

    bool elem_is_too_small(vector<indexed_value<T>> & row_chunk, indexed_value<T> & iv, int c_partial_pivoting);

    unsigned number_of_non_zeroes_in_row(unsigned row) const {
        return static_cast<unsigned>(m_rows[row].size());
    }

    unsigned number_of_non_zeroes_in_column(unsigned col) const {
        return m_columns[col].m_values.size();
    }

    bool shorten_columns_by_pivot_row(unsigned i, unsigned pivot_column);

    bool col_is_active(unsigned j, unsigned pivot) {
        return adjust_column_inverse(j) > pivot;
    }

    bool row_is_active(unsigned i, unsigned pivot) {
        return adjust_row_inverse(i) > pivot;
    }

    bool fill_eta_matrix(unsigned j, eta_matrix<T, X> ** eta);
#ifdef LEAN_DEBUG
    bool is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings & settings) const;

    bool is_upper_triangular_until(unsigned k) const;
    void check_column_vs_rows(unsigned col);

    void check_row_vs_columns(unsigned row);

    void check_rows_vs_columns();

    void check_columns_vs_rows();

    void check_matrix();
#endif
    void create_graph_G(const vector<unsigned> & active_rows, vector<unsigned> & sorted_active_rows);
    void process_column_recursively(unsigned i, vector<unsigned>  & sorted_rows);    
    void extend_and_sort_active_rows(const vector<unsigned> & active_rows, vector<unsigned> & sorted_active_rows);
    void process_index_recursively_for_y_U(unsigned j, vector<unsigned>  & sorted_rows);
    void resize(unsigned new_dim) {
        unsigned old_dim = dimension();
        lean_assert(new_dim >= old_dim);
        for (unsigned j = old_dim; j < new_dim; j++) {
            m_rows.push_back(vector<indexed_value<T>>());
            m_columns.push_back(col_header());
        }
        m_pivot_queue.resize(new_dim);
        m_row_permutation.resize(new_dim);
        m_column_permutation.resize(new_dim);
        m_work_pivot_vector.resize(new_dim);
        m_processed.resize(new_dim);
        for (unsigned j = old_dim; j < new_dim; j++) {
            add_new_element(j, j, numeric_traits<T>::one());
        }
    }
#ifdef LEAN_DEBUG
vector<T> get_full_row(unsigned i) const;
#endif
    unsigned pivot_queue_size() const { return m_pivot_queue.size(); }
};
};


