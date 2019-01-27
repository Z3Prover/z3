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

#include "util/vector.h"
#include "util/lp/square_sparse_matrix.h"
#include <set>
#include <queue>
namespace lp {
template <typename T, typename X>
template <typename M>
void square_sparse_matrix<T, X>::copy_column_from_input(unsigned input_column, const M& A, unsigned j) {
    vector<indexed_value<T>> & new_column_vector = m_columns[j].m_values;
    for (const auto & c : A.column(input_column)) {
        unsigned col_offset = static_cast<unsigned>(new_column_vector.size());
        vector<indexed_value<T>> & row_vector = m_rows[c.var()];
        unsigned row_offset = static_cast<unsigned>(row_vector.size());
        new_column_vector.push_back(indexed_value<T>(c.coeff(), c.var(), row_offset));
        row_vector.push_back(indexed_value<T>(c.coeff(), j, col_offset));
        m_n_of_active_elems++;
    }
}

template <typename T, typename X>
template <typename M>
void square_sparse_matrix<T, X>::copy_column_from_input_with_possible_zeros(const M& A, unsigned j) {
    vector<indexed_value<T>> & new_column_vector = m_columns[j].m_values;
    for (const auto & c : A.column(j)) {
        if (is_zero(c.coeff()))
            continue;
        unsigned col_offset = static_cast<unsigned>(new_column_vector.size());
        vector<indexed_value<T>> & row_vector = m_rows[c.var()];
        unsigned row_offset = static_cast<unsigned>(row_vector.size());
        new_column_vector.push_back(indexed_value<T>(c.coeff(), c.var(), row_offset));
        row_vector.push_back(indexed_value<T>(c.coeff(), j, col_offset));
        m_n_of_active_elems++;
    }
}

template <typename T, typename X>
template <typename M>
void square_sparse_matrix<T, X>::copy_from_input_on_basis(const M & A, vector<unsigned> & basis) {
    unsigned m = A.row_count();
    for (unsigned j = m; j-- > 0;) {
        copy_column_from_input(basis[j], A, j);
    }
}
template <typename T, typename X>
template <typename M>
void square_sparse_matrix<T, X>::copy_from_input(const M & A) {
    unsigned m = A.row_count();
    for (unsigned j = m; j-- > 0;) {
        copy_column_from_input_with_possible_zeros(A, j);
    }
}

// constructor that copies columns of the basis from A
template <typename T, typename X>
template <typename M>
square_sparse_matrix<T, X>::square_sparse_matrix(const M &A, vector<unsigned> & basis) :
    m_n_of_active_elems(0),
    m_pivot_queue(A.row_count()),
    m_row_permutation(A.row_count()),
    m_column_permutation(A.row_count()),
    m_work_pivot_vector(A.row_count(), -1),
    m_processed(A.row_count()) {
    init_row_headers();
    init_column_headers();
    copy_from_input_on_basis(A, basis);
}

template <typename T, typename X>
template <typename M>
square_sparse_matrix<T, X>::square_sparse_matrix(const M &A) :
    m_n_of_active_elems(0),
    m_pivot_queue(A.row_count()),
    m_row_permutation(A.row_count()),
    m_column_permutation(A.row_count()),
    m_work_pivot_vector(A.row_count(), -1),
    m_processed(A.row_count()) {
    init_row_headers();
    init_column_headers();
    copy_from_input(A);
}


template <typename T, typename X>
void square_sparse_matrix<T, X>::set_with_no_adjusting_for_row(unsigned row, unsigned col, T val) { // should not be used in efficient code
    vector<indexed_value<T>> & row_vec = m_rows[row];
    for (auto & iv : row_vec) {
        if (iv.m_index == col) {
            iv.set_value(val);
            return;
        }
    }
    // have not found the column between the indices
    row_vec.push_back(indexed_value<T>(val, col)); // what about m_other ???
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::set_with_no_adjusting_for_col(unsigned row, unsigned col, T val) { // should not be used in efficient code
    vector<indexed_value<T>> & col_vec = m_columns[col].m_values;
    for (auto & iv : col_vec) {
        if (iv.m_index == row) {
            iv.set_value(val);
            return;
        }
    }
    // have not found the column between the indices
    col_vec.push_back(indexed_value<T>(val, row)); // what about m_other ???
}


template <typename T, typename X>
void square_sparse_matrix<T, X>::set_with_no_adjusting(unsigned row, unsigned col, T val) { // should not be used in efficient code
    set_with_no_adjusting_for_row(row, col, val);
    set_with_no_adjusting_for_col(row, col, val);
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::set(unsigned row, unsigned col, T val) { // should not be used in efficient code
    lp_assert(row < dimension() && col < dimension());
    //            m_dense.set_elem(row, col, val);
    row = adjust_row(row);
    col = adjust_column(col);
    set_with_no_adjusting(row, col, val);
    //            lp_assert(*this == m_dense);
}

template <typename T, typename X>
T const & square_sparse_matrix<T, X>::get_not_adjusted(unsigned row, unsigned col) const {
    for (indexed_value<T> const & iv : m_rows[row]) {
        if (iv.m_index == col) {
            return iv.m_value;
        }
    }
    return numeric_traits<T>::zero();
}

template <typename T, typename X>
T const & square_sparse_matrix<T, X>::get(unsigned row, unsigned col) const { // should not be used in efficient code
    row = adjust_row(row);
    auto & row_chunk = m_rows[row];
    col = adjust_column(col);
    for (indexed_value<T> const & iv : row_chunk) {
        if (iv.m_index == col) {
            return iv.m_value;
        }
    }
    return numeric_traits<T>::zero();
}

// constructor creating a zero matrix of dim*dim
template <typename T, typename X>
square_sparse_matrix<T, X>::square_sparse_matrix(unsigned dim, unsigned ) :
    m_pivot_queue(dim), // dim will be the initial size of the queue
    m_row_permutation(dim),
    m_column_permutation(dim),
    m_work_pivot_vector(dim, -1),
    m_processed(dim) {
    init_row_headers();
    init_column_headers();
    }

template <typename T, typename X>
void square_sparse_matrix<T, X>::init_row_headers() {
    for (unsigned l = 0; l < m_row_permutation.size(); l++) {
        m_rows.push_back(vector<indexed_value<T>>());
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::init_column_headers() { // we always have only square square_sparse_matrix
    for (unsigned l = 0; l < m_row_permutation.size(); l++) {
        m_columns.push_back(col_header());
    }
}

template <typename T, typename X>
unsigned square_sparse_matrix<T, X>::lowest_row_in_column(unsigned j) {
    auto & mc = get_column_values(adjust_column(j));
    unsigned ret = 0;
    for (auto & iv : mc) {
        unsigned row = adjust_row_inverse(iv.m_index);
        if (row > ret) {
            ret = row;
        }
    }
    return ret;
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_element(vector<indexed_value<T>> & row_vals, unsigned row_offset, vector<indexed_value<T>> & column_vals, unsigned column_offset) {
    if (column_offset != column_vals.size() - 1) {
        auto & column_iv = column_vals[column_offset] = column_vals.back(); // copy from the tail
        column_iv_other(column_iv).m_other = column_offset;
        if (row_offset != row_vals.size() - 1) {
            auto & row_iv = row_vals[row_offset] = row_vals.back(); // copy from the tail
            row_iv_other(row_iv).m_other = row_offset;
        }
    } else if (row_offset != row_vals.size() - 1) {
        auto & row_iv = row_vals[row_offset] = row_vals.back(); // copy from the tail
        row_iv_other(row_iv).m_other = row_offset;
    }
    // do nothing - just decrease the sizes
    column_vals.pop_back();
    row_vals.pop_back();
    m_n_of_active_elems--; // the value is correct only when refactoring
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_element(vector<indexed_value<T>> & row_chunk, indexed_value<T> & row_el_iv) {
    auto & column_chunk = get_column_values(row_el_iv.m_index);
    indexed_value<T> & col_el_iv = column_chunk[row_el_iv.m_other];
    remove_element(row_chunk, col_el_iv.m_other, column_chunk, row_el_iv.m_other);
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::put_max_index_to_0(vector<indexed_value<T>> & row_vals, unsigned max_index)  {
    if (max_index == 0) return;
    indexed_value<T> * max_iv = & row_vals[max_index];
    indexed_value<T> * start_iv = & row_vals[0];
    // update the "other" columns elements which are bound to the start_iv and max_iv
    m_columns[max_iv->m_index].m_values[max_iv->m_other].m_other = 0;
    m_columns[start_iv->m_index].m_values[start_iv->m_other].m_other = max_index;

    // swap the elements
    indexed_value<T> t = * max_iv;
    * max_iv = * start_iv;
    * start_iv = t;
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::set_max_in_row(vector<indexed_value<T>> & row_vals) {
    if (row_vals.empty())
        return;
    T max_val = abs(row_vals[0].m_value);
    unsigned max_index = 0;
    for (unsigned i = 1; i <  row_vals.size(); i++) {
        T iabs = abs(row_vals[i].m_value);
        if (iabs > max_val) {
            max_val = iabs;
            max_index = i;
        }
    }
    put_max_index_to_0(row_vals, max_index);
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::pivot_with_eta(unsigned i, eta_matrix<T, X> *eta_matrix, lp_settings & settings) {
    const T& pivot = eta_matrix->get_diagonal_element();
    for (auto & it : eta_matrix->m_column_vector.m_data) {
        if (!pivot_row_to_row(i, it.second, it.first, settings)) {
            return false;
        }
    }

    divide_row_by_constant(i, pivot, settings);
    if (!shorten_active_matrix(i, eta_matrix)) {
        return false;
    }

    return true;
}

// returns the offset of the pivot column in the row
template <typename T, typename X>
void square_sparse_matrix<T, X>::scan_row_to_work_vector_and_remove_pivot_column(unsigned row, unsigned pivot_column) {
    auto & rvals = m_rows[row];
    unsigned size = rvals.size();
    for (unsigned j = 0; j < size; j++) {
        auto & iv = rvals[j];
        if (iv.m_index != pivot_column) {
            m_work_pivot_vector[iv.m_index] = j;
        } else {
            remove_element(rvals, iv);
            j--;
            size--;
        }
    }
}

#ifdef Z3DEBUG
template <typename T, typename X>
vector<T> square_sparse_matrix<T, X>::get_full_row(unsigned i) const {
    vector<T> r;
    for (unsigned j = 0; j < column_count(); j++)
        r.push_back(get(i, j));
    return r;
}
#endif



// This method pivots row i to row i0 by muliplying row i by
// alpha and adding it to row i0.
// After pivoting the row i0 has a max abs value set correctly at the beginning of m_start,
// Returns false if the resulting row is all zeroes, and true otherwise
template <typename T, typename X>
bool square_sparse_matrix<T, X>::pivot_row_to_row(unsigned i, const T& alpha, unsigned i0, lp_settings & settings ) {
    lp_assert(i < dimension() && i0 < dimension());
    lp_assert(i != i0);
    unsigned pivot_col = adjust_column(i);
    i = adjust_row(i);
    i0 = adjust_row(i0);
    vector<unsigned> became_zeros;
    // the offset of element of the pivot column in row i0
    scan_row_to_work_vector_and_remove_pivot_column(i0, pivot_col);
    auto & i0_row_vals = m_rows[i0];
    // run over the pivot row and update row i0
    unsigned prev_size_i0 = i0_row_vals.size();
    for (const auto & iv : m_rows[i]) {
        unsigned j = iv.m_index;
        if (j == pivot_col) continue;
        T alv = alpha * iv.m_value;
        int j_offs = m_work_pivot_vector[j];
        if (j_offs == -1) { // it is a new element
            if (!settings.abs_val_is_smaller_than_drop_tolerance(alv)) {
                add_new_element(i0, j, alv);
            }
        }
        else {
            auto & row_el_iv = i0_row_vals[j_offs];
            row_el_iv.m_value += alv;
            if (settings.abs_val_is_smaller_than_drop_tolerance(row_el_iv.m_value)) {
                became_zeros.push_back(j_offs);
                ensure_increasing(became_zeros);
            }
            else {
                m_columns[j].m_values[row_el_iv.m_other].set_value(row_el_iv.m_value);
            }
        }
    }
    
    
    // clean the work vector
    for (unsigned k = 0; k < prev_size_i0; k++) {
        m_work_pivot_vector[i0_row_vals[k].m_index] = -1;
    }

    for (unsigned k = became_zeros.size(); k-- > 0; ) {
        unsigned j = became_zeros[k];
        remove_element(i0_row_vals, i0_row_vals[j]);
        if (i0_row_vals.empty())
            return false;
    }

    if (numeric_traits<T>::precise() == false)
        set_max_in_row(i0_row_vals);
    
    return !i0_row_vals.empty();
}



// set the max val as well
// returns false if the resulting row is all zeroes, and true otherwise
template <typename T, typename X>
bool square_sparse_matrix<T, X>::set_row_from_work_vector_and_clean_work_vector_not_adjusted(unsigned i0, indexed_vector<T> & work_vec,
                                                                                      lp_settings & settings) {
    remove_zero_elements_and_set_data_on_existing_elements_not_adjusted(i0, work_vec, settings);
    // all non-zero elements in m_work_pivot_vector are new
    for (unsigned j : work_vec.m_index) {
        if (numeric_traits<T>::is_zero(work_vec[j])) {
            continue;
        }
        lp_assert(!settings.abs_val_is_smaller_than_drop_tolerance(work_vec[j]));
        add_new_element(i0, adjust_column(j), work_vec[j]);
        work_vec[j] = numeric_traits<T>::zero();
    }
    work_vec.m_index.clear();
    auto & row_vals = m_rows[i0];
    if (row_vals.empty()) {
        return false;
    }
    set_max_in_row(row_vals);  // it helps to find larger pivots
    return true;
}



template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_zero_elements_and_set_data_on_existing_elements(unsigned row) {
    auto & row_vals = m_rows[row];
    for (unsigned k = static_cast<unsigned>(row_vals.size()); k-- > 0;) { // we cannot simply run the iterator since we are removing
        // elements from row_vals
        auto & row_el_iv = row_vals[k];
        unsigned j = row_el_iv.m_index;
        T & wj = m_work_pivot_vector[j];
        if (is_zero(wj)) {
            remove_element(row_vals, row_el_iv);
        } else {
            m_columns[j].m_values[row_el_iv.m_other].set_value(wj);
            row_el_iv.set_value(wj);
            wj = zero_of_type<T>();
        }
    }
}

// work_vec here has not adjusted column indices
template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_zero_elements_and_set_data_on_existing_elements_not_adjusted(unsigned row, indexed_vector<T> & work_vec, lp_settings & settings) {
    auto & row_vals = m_rows[row];
    for (unsigned k = static_cast<unsigned>(row_vals.size()); k-- > 0;) { // we cannot simply run the iterator since we are removing
        // elements from row_vals
        auto & row_el_iv = row_vals[k];
        unsigned j = row_el_iv.m_index;
        unsigned rj = adjust_column_inverse(j);
        T val = work_vec[rj];
        if (settings.abs_val_is_smaller_than_drop_tolerance(val)) {
            remove_element(row_vals, row_el_iv);
            lp_assert(numeric_traits<T>::is_zero(val));
        } else {
            m_columns[j].m_values[row_el_iv.m_other].set_value(row_el_iv.m_value = val);
            work_vec[rj] = numeric_traits<T>::zero();
        }
    }
}


// adding delta columns at the end of the matrix
template <typename T, typename X>
void square_sparse_matrix<T, X>::add_columns_at_the_end(unsigned delta) {
    for (unsigned i = 0; i < delta; i++) {
        col_header col_head;
        m_columns.push_back(col_head);
    }
    m_column_permutation.enlarge(delta);
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::delete_column(int i) {
    lp_assert(i < dimension());
    for (auto cell = m_columns[i].m_head; cell != nullptr;) {
        auto next_cell = cell->m_down;
        kill_cell(cell);
        cell = next_cell;
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::divide_row_by_constant(unsigned i, const T & t, lp_settings & settings) {
    lp_assert(!settings.abs_val_is_smaller_than_zero_tolerance(t));
    i = adjust_row(i);
    for (auto & iv : m_rows[i]) {
        T &v = iv.m_value;
        v /= t;
        if (settings.abs_val_is_smaller_than_drop_tolerance(v)){
            v = numeric_traits<T>::zero();
        }
        m_columns[iv.m_index].m_values[iv.m_other].set_value(v);
    }
}


// solving x * this = y, and putting the answer into y
// the matrix here has to be upper triangular
template <typename T, typename X>
void square_sparse_matrix<T, X>::solve_y_U(vector<T> & y) const { // works by rows
#ifdef Z3DEBUG
    // T * rs = clone_vector<T>(y, dimension());
#endif
    unsigned end = dimension();
    for (unsigned i = 0; i + 1 < end; i++) {
        // all y[i] has correct values already
        const T & yv = y[i];
        if (numeric_traits<T>::is_zero(yv)) continue;
        auto & mc = get_row_values(adjust_row(i));
        for (auto & c : mc) {
            unsigned col = adjust_column_inverse(c.m_index);
            if (col != i) {
                y[col] -= c.m_value * yv;
            }
        }
    }
#ifdef Z3DEBUG
    // dense_matrix<T> deb(*this);
    // T * clone_y = clone_vector<T>(y, dimension());
    // deb.apply_from_right(clone_y);
    // lp_assert(vectors_are_equal(rs, clone_y, dimension()));
    // delete [] clone_y;
    // delete [] rs;
#endif
}

// solving x * this = y, and putting the answer into y
// the matrix here has to be upper triangular
template <typename T, typename X>
void square_sparse_matrix<T, X>::solve_y_U_indexed(indexed_vector<T> & y, const lp_settings & settings) {
#if 0 && Z3DEBUG
    vector<T> ycopy(y.m_data);
    if (numeric_traits<T>::precise() == false)
        solve_y_U(ycopy);
#endif
    vector<unsigned> sorted_active_columns;
    extend_and_sort_active_rows(y.m_index, sorted_active_columns);
    for (unsigned k = sorted_active_columns.size(); k-- > 0; ) {
        unsigned j = sorted_active_columns[k];
        auto & yj = y[j];
        for (auto & c: m_columns[adjust_column(j)].m_values) {
            unsigned i = adjust_row_inverse(c.m_index);
            if (i == j) continue;
            yj -= y[i] * c.m_value;
        }
    }
    y.m_index.clear();
    for (auto j : sorted_active_columns) {
        if (!settings.abs_val_is_smaller_than_drop_tolerance(y[j]))
            y.m_index.push_back(j);
        else if (!numeric_traits<T>::precise())
            y.m_data[j] = zero_of_type<T>();
    }

    lp_assert(y.is_OK());
#if 0 && Z3DEBUG
    if (numeric_traits<T>::precise() == false)
        lp_assert(vectors_are_equal(ycopy, y.m_data));
#endif
}


// fills the indices for such that y[i] can be not a zero
// sort them so the smaller indices come first
//    void fill_reachable_indices(std::set<unsigned> & rset, T *y) {
// std::queue<unsigned> q;
// int m = dimension();
// for (int i = m - 1; i >= 0; i--) {
//     if (!numeric_traits<T>::is_zero(y[i])){
//         for (cell * c = m_columns[adjust_column(i)].m_head; c != nullptr; c = c->m_down) {
//             unsigned row = adjust_row_inverse(c->m_i);
//             q.push(row);
//         }
//     }
// }
// while (!q.empty()) {
//     unsigned i = q.front();
//     q.pop();
//     for (cell * c = m_columns[adjust_column(i)].m_head; c != nullptr; c = c->m_down) {
//         unsigned row = adjust_row_inverse(c->m_i);
//         if (rset.find(row) == rset.end()){
//             rset.insert(row);
//             q.push(row);
//         }
//     }
//     }
// }

template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::find_error_in_solution_U_y(vector<L>& y_orig, vector<L> & y) {
    unsigned i = dimension();
    while (i--) {
        y_orig[i] -= dot_product_with_row(i, y);
    }
}

template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::find_error_in_solution_U_y_indexed(indexed_vector<L>& y_orig, indexed_vector<L> & y,  const vector<unsigned>& sorted_active_rows) {
    for (unsigned i: sorted_active_rows)
        y_orig.add_value_at_index(i, -dot_product_with_row(i, y)); // cannot round up here!!!
    // y_orig can contain very small values
}


template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::add_delta_to_solution(const vector<L>& del, vector<L> & y) {
    unsigned i = dimension();
    while (i--) {
        y[i] += del[i];
    }
}
template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::add_delta_to_solution(const indexed_vector<L>& del, indexed_vector<L> & y) {
//    lp_assert(del.is_OK());
 //   lp_assert(y.is_OK());
    for (auto i : del.m_index) {
        y.add_value_at_index(i, del[i]);
    }
}
template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::double_solve_U_y(indexed_vector<L>& y, const lp_settings & settings){
    lp_assert(y.is_OK());
    indexed_vector<L> y_orig(y); // copy y aside
    vector<unsigned> active_rows;
    solve_U_y_indexed_only(y, settings, active_rows);
    lp_assert(y.is_OK());
    find_error_in_solution_U_y_indexed(y_orig, y, active_rows);
    // y_orig contains the error now
    if (y_orig.m_index.size() * ratio_of_index_size_to_all_size<T>() < 32 * dimension()) {
        active_rows.clear();
        solve_U_y_indexed_only(y_orig, settings, active_rows);
        add_delta_to_solution(y_orig, y);
        y.clean_up();
    } else { // the dense version
        solve_U_y(y_orig.m_data);
        add_delta_to_solution(y_orig.m_data, y.m_data);
        y.restore_index_and_clean_from_data();
    }
    lp_assert(y.is_OK());
}
template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::double_solve_U_y(vector<L>& y){
    vector<L> y_orig(y); // copy y aside
    solve_U_y(y);
    find_error_in_solution_U_y(y_orig, y);
    // y_orig contains the error now
    solve_U_y(y_orig);
    add_delta_to_solution(y_orig, y);
}

// solving this * x = y, and putting the answer into y
// the matrix here has to be upper triangular
template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::solve_U_y(vector<L> & y) { // it is a column wise version
#ifdef Z3DEBUG
    // T * rs = clone_vector<T>(y, dimension());
#endif

    for (unsigned j = dimension(); j--; ) {
        const L & yj = y[j];
        if (is_zero(yj)) continue;
        for (const auto & iv : m_columns[adjust_column(j)].m_values) {
            unsigned i = adjust_row_inverse(iv.m_index);
            if (i != j) {
                y[i] -= iv.m_value * yj;
            }
        }
    }
#ifdef Z3DEBUG
    // dense_matrix<T> deb(*this);
    // T * clone_y = clone_vector<T>(y, dimension());
    // deb.apply_from_left(clone_y);
    // lp_assert(vectors_are_equal(rs, clone_y, dimension()));
#endif
}
template <typename T, typename X>
void square_sparse_matrix<T, X>::process_index_recursively_for_y_U(unsigned j, vector<unsigned> & sorted_active_rows) {
    lp_assert(m_processed[j] == false);
    m_processed[j]=true;
    auto & row = m_rows[adjust_row(j)];
    for (auto & c : row) {
        unsigned i = adjust_column_inverse(c.m_index);
        if (i == j) continue;
        if (!m_processed[i]) {
            process_index_recursively_for_y_U(i, sorted_active_rows);
        }
    }
    sorted_active_rows.push_back(j);
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::process_column_recursively(unsigned j, vector<unsigned> & sorted_active_rows) {
    lp_assert(m_processed[j] == false);
    auto & mc = m_columns[adjust_column(j)].m_values;
    for (auto & iv : mc) {
        unsigned i = adjust_row_inverse(iv.m_index);
        if (i == j) continue;
        if (!m_processed[i]) {
            process_column_recursively(i, sorted_active_rows);
        }
    }
    m_processed[j]=true;
    sorted_active_rows.push_back(j);
}


template <typename T, typename X>
void square_sparse_matrix<T, X>::create_graph_G(const vector<unsigned> & index_or_right_side, vector<unsigned> & sorted_active_rows) {
    for (auto i : index_or_right_side) {
        if (m_processed[i]) continue;
        process_column_recursively(i, sorted_active_rows);
    }

    for (auto i : sorted_active_rows) {
        m_processed[i] = false;
    }
}


template <typename T, typename X>
void square_sparse_matrix<T, X>::extend_and_sort_active_rows(const vector<unsigned> & index_or_right_side, vector<unsigned> & sorted_active_rows) {
    for (auto i : index_or_right_side) {
        if (m_processed[i]) continue;
        process_index_recursively_for_y_U(i, sorted_active_rows);
    }

    for (auto i : sorted_active_rows) {
        m_processed[i] = false;
    }
}


template <typename T, typename X>
template <typename L>
void square_sparse_matrix<T, X>::solve_U_y_indexed_only(indexed_vector<L> & y, const lp_settings & settings, vector<unsigned> & sorted_active_rows) { // it is a column wise version
    create_graph_G(y.m_index, sorted_active_rows);

    for (auto k = sorted_active_rows.size(); k-- > 0;) {
        unsigned j = sorted_active_rows[k];
        const L & yj = y[j];
        if (is_zero(yj)) continue;
        auto & mc = m_columns[adjust_column(j)].m_values;
        for (auto & iv : mc) {
            unsigned i = adjust_row_inverse(iv.m_index);
            if (i != j) {
                y[i] -= iv.m_value * yj;
            }
        }
    }
    y.m_index.clear();
    for (auto j : sorted_active_rows) {
        if (!settings.abs_val_is_smaller_than_drop_tolerance(y[j]))
            y.m_index.push_back(j);
        else if (!numeric_traits<L>::precise())
            y[j] = zero_of_type<L>();
    }

    lp_assert(y.is_OK());
#ifdef Z3DEBUG
     // dense_matrix<T,X> deb(this);
     // vector<T> clone_y(y.m_data);
     // deb.apply_from_left(clone_y);
     // lp_assert(vectors_are_equal(rs, clone_y));
#endif
}

template <typename T, typename X>
template <typename L>
L square_sparse_matrix<T, X>::dot_product_with_row (unsigned row, const vector<L> & y) const {
    L ret = zero_of_type<L>();
    auto & mc = get_row_values(adjust_row(row));
    for (auto & c : mc) {
        unsigned col = m_column_permutation[c.m_index];
        ret += c.m_value * y[col];
    }
    return ret;
}

template <typename T, typename X>
template <typename L>
L square_sparse_matrix<T, X>::dot_product_with_row (unsigned row, const indexed_vector<L> & y) const {
    L ret = zero_of_type<L>();
    auto & mc = get_row_values(adjust_row(row));
    for (auto & c : mc) {
        unsigned col = m_column_permutation[c.m_index];
        ret += c.m_value * y[col];
    }
    return ret;
}


template <typename T, typename X>
unsigned square_sparse_matrix<T, X>::get_number_of_nonzeroes() const {
    unsigned ret = 0;
    for (unsigned i = dimension(); i--; ) {
        ret += number_of_non_zeroes_in_row(i);
    }
    return ret;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::get_non_zero_column_in_row(unsigned i, unsigned *j) const {
    // go over the i-th row
    auto & mc = get_row_values(adjust_row(i));
    if (mc.size() > 0) {
        *j = m_column_permutation[mc[0].m_index];
        return true;
    }
    return false;
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_element_that_is_not_in_w(vector<indexed_value<T>> & column_vals, indexed_value<T> & col_el_iv) {
    auto & row_chunk = m_rows[col_el_iv.m_index];
    indexed_value<T> & row_el_iv = row_chunk[col_el_iv.m_other];
    unsigned index_in_row = col_el_iv.m_other;
    remove_element(row_chunk, col_el_iv.m_other, column_vals, row_el_iv.m_other);
    if (index_in_row == 0)
        set_max_in_row(row_chunk);
}


// w contains the new column
// the old column inside of the matrix has not been changed yet
template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_elements_that_are_not_in_w_and_update_common_elements(unsigned column_to_replace, indexed_vector<T> & w) {
    // --------------------------------
    // column_vals represents the old column
    auto & column_vals = m_columns[column_to_replace].m_values;
    for (unsigned k = static_cast<unsigned>(column_vals.size()); k-- > 0;) {
        indexed_value<T> & col_el_iv = column_vals[k];
        unsigned i = col_el_iv.m_index;
        T &w_data_at_i = w[adjust_row_inverse(i)];
        if (numeric_traits<T>::is_zero(w_data_at_i)) {
            remove_element_that_is_not_in_w(column_vals, col_el_iv);
        } else {
            auto& row_chunk = m_rows[i];
            unsigned index_in_row = col_el_iv.m_other;
            if (index_in_row == 0) {
                bool look_for_max = abs(w_data_at_i) < abs(row_chunk[0].m_value);
                row_chunk[0].set_value(col_el_iv.m_value = w_data_at_i);
                if (look_for_max)
                    set_max_in_row(i);
            } else {
                row_chunk[index_in_row].set_value(col_el_iv.m_value = w_data_at_i);
                if (abs(w_data_at_i) > abs(row_chunk[0].m_value))
                    put_max_index_to_0(row_chunk, index_in_row);
            }
            w_data_at_i = numeric_traits<T>::zero();
        }
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::add_new_element(unsigned row, unsigned col, const T& val) {
    auto & row_vals = m_rows[row];
    auto & col_vals = m_columns[col].m_values;
    unsigned row_el_offs = static_cast<unsigned>(row_vals.size());
    unsigned col_el_offs = static_cast<unsigned>(col_vals.size());
    row_vals.push_back(indexed_value<T>(val, col, col_el_offs));
    col_vals.push_back(indexed_value<T>(val, row, row_el_offs));
    m_n_of_active_elems++;
}

// w contains the "rest" of the new column; all common elements of w and the old column has been zeroed
// the old column inside of the matrix has not been changed yet
template <typename T, typename X>
void square_sparse_matrix<T, X>::add_new_elements_of_w_and_clear_w(unsigned column_to_replace, indexed_vector<T> & w, lp_settings & settings) {
    for (unsigned i : w.m_index) {
        T w_at_i = w[i];
        if (numeric_traits<T>::is_zero(w_at_i)) continue; // was dealt with already
        if (!settings.abs_val_is_smaller_than_drop_tolerance(w_at_i)) {
            unsigned ai = adjust_row(i);
            add_new_element(ai, column_to_replace, w_at_i);
            auto & row_chunk = m_rows[ai];
            lp_assert(row_chunk.size() > 0);
            if (abs(w_at_i) > abs(row_chunk[0].m_value))
                put_max_index_to_0(row_chunk, static_cast<unsigned>(row_chunk.size()) - 1);
        }
        w[i] = numeric_traits<T>::zero();
    }
    w.m_index.clear();
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::replace_column(unsigned column_to_replace, indexed_vector<T> & w, lp_settings &settings) {
    column_to_replace = adjust_column(column_to_replace);
    remove_elements_that_are_not_in_w_and_update_common_elements(column_to_replace, w);
    add_new_elements_of_w_and_clear_w(column_to_replace, w, settings);
}

template <typename T, typename X>
unsigned square_sparse_matrix<T, X>::pivot_score(unsigned i, unsigned j) {
    // It goes like this (rnz-1)(cnz-1) is the Markovitz number, that is the max number of
    // new non zeroes we can obtain after the pivoting.
    // In addition we will get another cnz - 1 elements in the eta matrix created for this pivot,
    // which gives rnz(cnz-1). For example, is 0 for a column singleton, but not for
    // a row singleton ( which is not a column singleton).

    auto col_header = m_columns[j];

    return static_cast<unsigned>(get_row_values(i).size() * (col_header.m_values.size() - col_header.m_shortened_markovitz - 1));
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::enqueue_domain_into_pivot_queue() {
    lp_assert(m_pivot_queue.size() == 0);
    for (unsigned i = 0; i < dimension(); i++) {
        auto & rh = m_rows[i];
        unsigned rnz = static_cast<unsigned>(rh.size());
        for (auto iv : rh) {
            unsigned j = iv.m_index;
            m_pivot_queue.enqueue(i, j, rnz * (static_cast<unsigned>(m_columns[j].m_values.size()) - 1));
        }
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::set_max_in_rows() {
    unsigned i = dimension();
    while (i--)
        set_max_in_row(i);
}


template <typename T, typename X>
void square_sparse_matrix<T, X>::zero_shortened_markovitz_numbers() {
    for (auto & ch : m_columns)
        ch.zero_shortened_markovitz();
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::prepare_for_factorization() {
    zero_shortened_markovitz_numbers();
    set_max_in_rows();
    enqueue_domain_into_pivot_queue();
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::recover_pivot_queue(vector<upair> & rejected_pivots)  {
    for (auto p : rejected_pivots) {
        m_pivot_queue.enqueue(p.first, p.second, pivot_score(p.first, p.second));
    }
}

template <typename T, typename X>
int square_sparse_matrix<T, X>::elem_is_too_small(unsigned i, unsigned j, int c_partial_pivoting)  {
    auto & row_chunk = m_rows[i];

    if (j == row_chunk[0].m_index) {
        return 0; // the max element is at the head
    }
    T max = abs(row_chunk[0].m_value);
    for (unsigned k = 1; k < row_chunk.size(); k++) {
        auto &iv = row_chunk[k];
        if (iv.m_index == j)
            return abs(iv.m_value) * c_partial_pivoting < max ? 1: 0;
    }
    return 2;  // the element became zero but it still sits in the active pivots?
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::remove_row_from_active_pivots_and_shorten_columns(unsigned row) {
    unsigned arow = adjust_row(row);
    for (auto & iv : m_rows[arow]) {
        m_pivot_queue.remove(arow, iv.m_index);
        m_n_of_active_elems--;  // the value is correct only when refactoring
        if (adjust_column_inverse(iv.m_index) <= row)
            continue; // this column will be removed anyway
        auto & col = m_columns[iv.m_index];

        col.shorten_markovich_by_one();
        if (col.m_values.size() <= col.m_shortened_markovitz)
            return false; // got a zero column
    }
    return true;
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::remove_pivot_column(unsigned row) {
    unsigned acol = adjust_column(row);
    for (const auto & iv : m_columns[acol].m_values)
        if (adjust_row_inverse(iv.m_index) >= row)
            m_pivot_queue.remove(iv.m_index, acol);
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::update_active_pivots(unsigned row) {
    unsigned arow = adjust_row(row);
    for (const auto & iv : m_rows[arow]) {
        col_header & ch = m_columns[iv.m_index];
        int cols = static_cast<int>(ch.m_values.size()) - ch.m_shortened_markovitz - 1;
        lp_assert(cols >= 0);
        for (const auto &ivc : ch.m_values) {
            unsigned i = ivc.m_index;
            if (adjust_row_inverse(i) <= row) continue; // the i is not an active row
            m_pivot_queue.enqueue(i, iv.m_index, static_cast<unsigned>(m_rows[i].size())*cols);
        }
    }
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::shorten_active_matrix(unsigned row, eta_matrix<T, X> *eta_matrix) {
    if (!remove_row_from_active_pivots_and_shorten_columns(row))
        return false;
    remove_pivot_column(row);
    // need to know the max priority of the queue here
    update_active_pivots(row);
    if (eta_matrix == nullptr) return true;
    // it looks like double work, but the pivot scores have changed for all rows
    // touched by eta_matrix
    for (auto & it : eta_matrix->m_column_vector.m_data) {
        unsigned row = adjust_row(it.first);
        const auto & row_values = m_rows[row];
        unsigned rnz = static_cast<unsigned>(row_values.size());
        for (auto & iv : row_values) {
            const col_header& ch = m_columns[iv.m_index];
            int cnz = static_cast<int>(ch.m_values.size()) - ch.m_shortened_markovitz - 1;
            lp_assert(cnz >= 0);
            m_pivot_queue.enqueue(row, iv.m_index, rnz * cnz);
        }
    }

    return true;
}

template <typename T, typename X>
unsigned square_sparse_matrix<T, X>::pivot_score_without_shortened_counters(unsigned i, unsigned j, unsigned k) {
    auto &cols = m_columns[j].m_values;
    unsigned cnz = cols.size();
    for (auto & iv : cols) {
        if (adjust_row_inverse(iv.m_index) < k)
            cnz--;
    }
    lp_assert(cnz > 0);
    return m_rows[i].m_values.size() * (cnz - 1);
}
#ifdef Z3DEBUG
template <typename T, typename X>
bool square_sparse_matrix<T, X>::can_improve_score_for_row(unsigned row, unsigned score, T const & c_partial_pivoting, unsigned k) {
    unsigned arow = adjust_row(row);
    auto & row_vals = m_rows[arow].m_values;
    auto & begin_iv = row_vals[0];
    T row_max = abs(begin_iv.m_value);
    lp_assert(adjust_column_inverse(begin_iv.m_index) >= k);
    if (pivot_score_without_shortened_counters(arow, begin_iv.m_index, k) < score) {
        print_active_matrix(k);
        return true;
    }
    for (unsigned jj = 1; jj < row_vals.size(); jj++) {
        auto & iv = row_vals[jj];
        lp_assert(adjust_column_inverse(iv.m_index) >= k);
        lp_assert(abs(iv.m_value) <= row_max);
        if (c_partial_pivoting * abs(iv.m_value) < row_max) continue;
        if (pivot_score_without_shortened_counters(arow, iv.m_index, k) < score) {
            print_active_matrix(k);
            return true;
        }
    }
    return false;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::really_best_pivot(unsigned i, unsigned j, T const & c_partial_pivoting, unsigned k) {
    unsigned queue_pivot_score = pivot_score_without_shortened_counters(i, j, k);
    for (unsigned ii = k; ii < dimension(); ii++) {
        lp_assert(!can_improve_score_for_row(ii, queue_pivot_score, c_partial_pivoting, k));
    }
    return true;
}
template <typename T, typename X>
void square_sparse_matrix<T, X>::print_active_matrix(unsigned k, std::ostream & out) {
    out << "active matrix for k = " << k << std::endl;
    if (k >= dimension()) {
        out << "empty" << std::endl;
        return;
    }
    unsigned dim = dimension() - k;
    dense_matrix<T, X> b(dim, dim);
    for (unsigned i = 0; i < dim; i++)
        for (unsigned j = 0; j < dim; j++ )
            b.set_elem(i, j, zero_of_type<T>());
    for (int i = k; i < dimension(); i++) {
        unsigned col = adjust_column(i);
        for (auto &iv : get_column_values(col)) {
            unsigned row = iv.m_index;
            unsigned row_ex = this->adjust_row_inverse(row);
            if (row_ex < k) continue;
            auto v = this->get_not_adjusted(row, col);
            b.set_elem(row_ex - k, i -k, v);
        }
    }
    print_matrix(b, out);
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::pivot_queue_is_correct_for_row(unsigned i, unsigned k) {
    unsigned arow = adjust_row(i);
    for (auto & iv : m_rows[arow].m_values) {
        lp_assert(pivot_score_without_shortened_counters(arow, iv.m_index, k + 1) ==
                    m_pivot_queue.get_priority(arow, iv.m_index));
    }
    return true;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::pivot_queue_is_correct_after_pivoting(int k) {
    for (unsigned i = k + 1; i < dimension(); i++ )
        lp_assert(pivot_queue_is_correct_for_row(i, k));
    lp_assert(m_pivot_queue.is_correct());
    return true;
}
#endif

template <typename T, typename X>
bool square_sparse_matrix<T, X>::get_pivot_for_column(unsigned &i, unsigned &j, int c_partial_pivoting, unsigned k) {
    vector<upair> pivots_candidates_that_are_too_small;
    while (!m_pivot_queue.is_empty()) {
        m_pivot_queue.dequeue(i, j);
        unsigned i_inv = adjust_row_inverse(i);
        if (i_inv < k) continue;
        unsigned j_inv = adjust_column_inverse(j);
        if (j_inv < k) continue;
        int _small = elem_is_too_small(i, j, c_partial_pivoting);
        if (!_small) {
#ifdef Z3DEBUG
            // if (!really_best_pivot(i, j, c_partial_pivoting, k)) {
            //     print_active_matrix(k);
            //     lp_assert(false);
            //  }
#endif
            recover_pivot_queue(pivots_candidates_that_are_too_small);
            i = i_inv;
            j = j_inv;
            return true;
        }
        if (_small != 2) { // 2 means that the pair is not in the matrix
            pivots_candidates_that_are_too_small.push_back(std::make_pair(i, j));
        }
    }
    recover_pivot_queue(pivots_candidates_that_are_too_small);
    return false;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::elem_is_too_small(vector<indexed_value<T>> & row_chunk, indexed_value<T> & iv, int c_partial_pivoting) {
    if (&iv == &row_chunk[0]) {
        return false; // the max element is at the head
    }
    T val = abs(iv.m_value);
    T max = abs(row_chunk[0].m_value);
    return val * c_partial_pivoting < max;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::shorten_columns_by_pivot_row(unsigned i, unsigned pivot_column) {
    vector<indexed_value<T>> & row_chunk = get_row_values(i);

    for (indexed_value<T> & iv : row_chunk) {
        unsigned j = iv.m_index;
        if (j == pivot_column) {
            lp_assert(!col_is_active(j));
            continue;
        }
        m_columns[j].shorten_markovich_by_one();

        if (m_columns[j].m_shortened_markovitz >= get_column_values(j).size()) { // got the zero column under the row!
            return false;
        }
    }
    return true;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::fill_eta_matrix(unsigned j, eta_matrix<T, X> ** eta) {
    const vector<indexed_value<T>> & col_chunk = get_column_values(adjust_column(j));
    bool is_unit = true;
    for (const auto & iv : col_chunk) {
        unsigned i = adjust_row_inverse(iv.m_index);
        if (i > j) {
            is_unit = false;
            break;
        }
        if (i == j && iv.m_value != 1) {
            is_unit = false;
            break;
        }
    }

    if (is_unit) {
        *eta = nullptr;
        return true;
    }

#ifdef Z3DEBUG
    *eta = new eta_matrix<T, X>(j, dimension());
#else
    *eta = new eta_matrix<T, X>(j);
#endif
    for (const auto & iv : col_chunk) {
        unsigned i = adjust_row_inverse(iv.m_index);
        if (i < j) {
            continue;
        }
        if (i > j) {
            (*eta)->push_back(i, - iv.m_value);
        } else { // i == j
            if ( !(*eta)->set_diagonal_element(iv.m_value)) {
                delete *eta;
                *eta = nullptr;
                return false;
            }
                
        }
    }
        
    (*eta)->divide_by_diagonal_element();
    return true;
}
#ifdef Z3DEBUG
template <typename T, typename X>
bool square_sparse_matrix<T, X>::is_upper_triangular_and_maximums_are_set_correctly_in_rows(lp_settings & settings) const {
    for (unsigned i = 0; i < dimension(); i++) {
        vector<indexed_value<T>> const & row_chunk = get_row_values(i);
        lp_assert(row_chunk.size());
        T const & max = abs(row_chunk[0].m_value);
        unsigned ai = adjust_row_inverse(i);
        for (auto & iv : row_chunk) {
            lp_assert(abs(iv.m_value) <= max);
            unsigned aj = adjust_column_inverse(iv.m_index);
            if (!(ai <= aj || numeric_traits<T>::is_zero(iv.m_value)))
                return false;
            if (aj == ai) {
                if (iv.m_value != 1) {
                    return false;
                }
            }
            if (settings.abs_val_is_smaller_than_drop_tolerance(iv.m_value) && (!is_zero(iv.m_value)))
                return false;
        }
    }
    return true;
}

template <typename T, typename X>
bool square_sparse_matrix<T, X>::is_upper_triangular_until(unsigned k) const {
    for (unsigned j = 0; j < dimension() && j < k; j++) {
        unsigned aj = adjust_column(j);
        auto & col = get_column_values(aj);
        for (auto & iv : col) {
            unsigned row = adjust_row_inverse(iv.m_index);
            if (row > j)
                return false;
        }
    }
    return true;
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::check_column_vs_rows(unsigned col) {
    auto & mc = get_column_values(col);
    for (indexed_value<T> & column_iv : mc) {
        indexed_value<T> & row_iv = column_iv_other(column_iv);
        if (row_iv.m_index != col) {
            lp_assert(false);
        }

        if (& row_iv_other(row_iv) != &column_iv) {
            lp_assert(false);
        }

        if (row_iv.m_value != column_iv.m_value) {
            lp_assert(false);
        }
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::check_row_vs_columns(unsigned row) {
    auto & mc = get_row_values(row);
    for (indexed_value<T> & row_iv : mc) {
        indexed_value<T> & column_iv = row_iv_other(row_iv);

        if (column_iv.m_index != row) {
            lp_assert(false);
        }

        if (& row_iv != & column_iv_other(column_iv)) {
            lp_assert(false);
        }

        if (row_iv.m_value != column_iv.m_value) {
            lp_assert(false);
        }
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::check_rows_vs_columns() {
    for (unsigned i = 0; i < dimension(); i++) {
        check_row_vs_columns(i);
    }
}

template <typename T, typename X>
void square_sparse_matrix<T, X>::check_columns_vs_rows() {
    for (unsigned i = 0; i < dimension(); i++) {
        check_column_vs_rows(i);
    }
}
template <typename T, typename X>
void square_sparse_matrix<T, X>::check_matrix() {
    check_rows_vs_columns();
    check_columns_vs_rows();
}
#endif
}

