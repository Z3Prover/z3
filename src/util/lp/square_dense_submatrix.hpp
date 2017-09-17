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
#include "util/lp/square_dense_submatrix.h"
namespace lp {
template <typename T, typename X>
square_dense_submatrix<T, X>::square_dense_submatrix (sparse_matrix<T, X> *parent_matrix, unsigned index_start) :
    m_index_start(index_start),
    m_dim(parent_matrix->dimension() - index_start),
    m_v(m_dim * m_dim),
    m_parent(parent_matrix),
    m_row_permutation(m_parent->dimension()),
    m_column_permutation(m_parent->dimension()) {
    int row_offset = - static_cast<int>(m_index_start);
    for (unsigned i = index_start; i < parent_matrix->dimension(); i++) {
        unsigned row = parent_matrix->adjust_row(i);
        for (auto & iv : parent_matrix->get_row_values(row)) {
            unsigned j = parent_matrix->adjust_column_inverse(iv.m_index);
            SASSERT(j>= m_index_start);
            m_v[row_offset + j] = iv.m_value;
        }
        row_offset += m_dim;
    }
}

template <typename T, typename X> void square_dense_submatrix<T, X>::init(sparse_matrix<T, X> *parent_matrix, unsigned index_start) {
    m_index_start = index_start;
    m_dim = parent_matrix->dimension() - index_start;
    m_v.resize(m_dim * m_dim);
    m_parent = parent_matrix;
    m_column_permutation.init(m_parent->dimension());
    for (unsigned i = index_start; i < parent_matrix->dimension(); i++) {
        unsigned row = parent_matrix->adjust_row(i);
        for (auto & iv : parent_matrix->get_row_values(row)) {
            unsigned j = parent_matrix->adjust_column_inverse(iv.m_index);
            (*this)[i][j] = iv.m_value;
        }
    }
}

template <typename T, typename X>    int square_dense_submatrix<T, X>::find_pivot_column_in_row(unsigned i) const {
    int j = -1;
    T max = zero_of_type<T>();
    SASSERT(i >= m_index_start);
    unsigned row_start = (i - m_index_start) * m_dim;
    for (unsigned k = i; k < m_parent->dimension(); k++) {
        unsigned col = adjust_column(k); // this is where the column is in the row
        unsigned offs = row_start + col - m_index_start;
        T t = abs(m_v[offs]);
        if (t > max) {
            j = k;
            max = t;
        }
    }
    return j;
}

template <typename T, typename X>    void square_dense_submatrix<T, X>::pivot(unsigned i, lp_settings & settings) {
    divide_row_by_pivot(i);
    for (unsigned k = i + 1; k < m_parent->dimension(); k++)
        pivot_row_to_row(i, k, settings);
}

template <typename T, typename X>    void square_dense_submatrix<T, X>::pivot_row_to_row(unsigned i, unsigned row, lp_settings & settings) {
    SASSERT(i < row);
    unsigned pj = adjust_column(i); // the pivot column
    unsigned pjd = pj - m_index_start;
    unsigned pivot_row_offset = (i-m_index_start)*m_dim;
    T pivot = m_v[pivot_row_offset + pjd];
    unsigned row_offset= (row-m_index_start)*m_dim;
    T m = m_v[row_offset + pjd];
    SASSERT(!is_zero(pivot));
    m_v[row_offset + pjd] = -m * pivot; // creating L matrix
    for (unsigned j = m_index_start; j < m_parent->dimension(); j++) {
        if (j == pj) {
            pivot_row_offset++;
            row_offset++;
            continue;
        }
        auto t = m_v[row_offset] - m_v[pivot_row_offset] * m;
        if (settings.abs_val_is_smaller_than_drop_tolerance(t)) {
            m_v[row_offset] = zero_of_type<T>();
        } else {
            m_v[row_offset] = t;
        }
        row_offset++; pivot_row_offset++;
        // at the same time we pivot the L too
    }
}

template <typename T, typename X>    void square_dense_submatrix<T, X>::divide_row_by_pivot(unsigned i) {
    unsigned pj = adjust_column(i); // the pivot column
    unsigned irow_offset = (i - m_index_start) * m_dim;
    T pivot = m_v[irow_offset + pj - m_index_start];
    SASSERT(!is_zero(pivot));
    for (unsigned k = m_index_start; k < m_parent->dimension(); k++) {
        if (k == pj){
            m_v[irow_offset++] = one_of_type<T>() / pivot; // creating the L matrix diagonal
            continue;
        }
        m_v[irow_offset++] /= pivot;
    }
}

template <typename T, typename X>    void square_dense_submatrix<T, X>::update_parent_matrix(lp_settings & settings) {
    for (unsigned i = m_index_start; i < m_parent->dimension(); i++)
        update_existing_or_delete_in_parent_matrix_for_row(i, settings);
    push_new_elements_to_parent_matrix(settings);
    for (unsigned i = m_index_start; i < m_parent->dimension(); i++)
        m_parent->set_max_in_row(m_parent->adjust_row(i));
}

template <typename T, typename X>    void square_dense_submatrix<T, X>::update_existing_or_delete_in_parent_matrix_for_row(unsigned i, lp_settings & settings) {
    bool diag_updated = false;
    unsigned ai = m_parent->adjust_row(i);
    auto & row_vals = m_parent->get_row_values(ai);
    for (unsigned k = 0; k < row_vals.size(); k++) {
        auto & iv = row_vals[k];
        unsigned j = m_parent->adjust_column_inverse(iv.m_index);
        if (j < i) {
            m_parent->remove_element(row_vals, iv);
            k--;
        } else if (i == j) {
            m_parent->m_columns[iv.m_index].m_values[iv.m_other].set_value(iv.m_value = one_of_type<T>());
            diag_updated = true;
        } else { // j > i
            T & v = (*this)[i][j];
            if (settings.abs_val_is_smaller_than_drop_tolerance(v)) {
                m_parent->remove_element(row_vals, iv);
                k--;
            } else {
                m_parent->m_columns[iv.m_index].m_values[iv.m_other].set_value(iv.m_value = v);
                v = zero_of_type<T>(); // only new elements are left above the diagonal
            }
        }
    }
    if (!diag_updated) {
        unsigned aj = m_parent->adjust_column(i);
        m_parent->add_new_element(ai, aj, one_of_type<T>());
    }
}

template <typename T, typename X>    void square_dense_submatrix<T, X>::push_new_elements_to_parent_matrix(lp_settings & settings) {
    for (unsigned i = m_index_start; i < m_parent->dimension() - 1; i++) {
        unsigned ai = m_parent->adjust_row(i);
        for (unsigned j = i + 1; j < m_parent->dimension(); j++) {
            T & v = (*this)[i][j];
            if (!settings.abs_val_is_smaller_than_drop_tolerance(v)) {
                unsigned aj = m_parent->adjust_column(j);
                m_parent->add_new_element(ai, aj, v);
            }
            v = zero_of_type<T>(); // leave only L elements now
        }
    }
}
template <typename T, typename X>
template <typename L>
L square_dense_submatrix<T, X>::row_by_vector_product(unsigned i, const vector<L> & v) {
    SASSERT(i >= m_index_start);

    unsigned row_in_subm = i - m_index_start;
    unsigned row_offset = row_in_subm * m_dim;
    L r = zero_of_type<L>();
    for (unsigned j = 0; j < m_dim; j++)
        r += m_v[row_offset + j] * v[adjust_column_inverse(m_index_start + j)];
    return r;
}

template <typename T, typename X>
template <typename L>
L square_dense_submatrix<T, X>::column_by_vector_product(unsigned j, const vector<L> & v) {
    SASSERT(j >= m_index_start);

    unsigned offset = j - m_index_start;
    L r = zero_of_type<L>();
    for (unsigned i = 0; i < m_dim; i++, offset += m_dim)
        r += m_v[offset] * v[adjust_row_inverse(m_index_start + i)];
    return r;
}
template <typename T, typename X>
template <typename L>
L square_dense_submatrix<T, X>::row_by_indexed_vector_product(unsigned i, const indexed_vector<L> & v) {
    SASSERT(i >= m_index_start);

    unsigned row_in_subm = i - m_index_start;
    unsigned row_offset = row_in_subm * m_dim;
    L r = zero_of_type<L>();
    for (unsigned j = 0; j < m_dim; j++)
        r += m_v[row_offset + j] * v[adjust_column_inverse(m_index_start + j)];
    return r;
}
template <typename T, typename X>
template <typename L>
void square_dense_submatrix<T, X>::apply_from_left_local(indexed_vector<L> & w, lp_settings & settings) {
#ifdef Z3DEBUG
    // dense_matrix<T, X> deb(*this);
    // vector<L>  deb_w(w.m_data.size());
    // for (unsigned i = 0; i < w.m_data.size(); i++)
    //     deb_w[i] = w[i];

    // deb.apply_from_left(deb_w);
#endif // use indexed vector here

#ifndef DO_NOT_USE_INDEX
    vector<L> t(m_parent->dimension(), zero_of_type<L>());
    for (auto k : w.m_index) {
        unsigned j = adjust_column(k); // k-th element will contribute only to column j
        if (j < m_index_start || j >= this->m_index_start +  this->m_dim) { // it is a unit matrix outside 
            t[adjust_row_inverse(j)] = w[k];
        } else {
            const L & v = w[k];
            for (unsigned i = 0; i < m_dim; i++) {
                unsigned row = adjust_row_inverse(m_index_start + i);
                unsigned offs = i * m_dim + j - m_index_start;
                t[row] += m_v[offs] * v;
            }
        }
    }
    w.m_index.clear();
    for (unsigned i = 0; i < m_parent->dimension(); i++) {
        const L & v = t[i];
        if (!settings.abs_val_is_smaller_than_drop_tolerance(v)){
            w.m_index.push_back(i);
            w.m_data[i] = v;
        } else {
            w.m_data[i] = zero_of_type<L>();
        }
    }
#else
    vector<L> t(m_parent->dimension());
    for (unsigned i = 0; i < m_index_start; i++) {
        t[adjust_row_inverse(i)] = w[adjust_column_inverse(i)];
    }
    for (unsigned i = m_index_start; i < m_parent->dimension(); i++){
        t[adjust_row_inverse(i)] = row_by_indexed_vector_product(i, w);
    }
    for (unsigned i = 0; i < m_parent->dimension(); i++) {
        w.set_value(t[i], i);
    }
    for (unsigned i = 0; i < m_parent->dimension(); i++) {
        const L & v = t[i];
        if (!is_zero(v))
            w.m_index.push_back(i);
        w.m_data[i] = v;
    }
#endif
#ifdef Z3DEBUG
    // cout << "w final" << endl;
    // print_vector(w.m_data);
    //        SASSERT(vectors_are_equal<T>(deb_w, w.m_data));
    // SASSERT(w.is_OK());
#endif
}

template <typename T, typename X>
template <typename L>
void square_dense_submatrix<T, X>::apply_from_left_to_vector(vector<L> & w) {
    // lp_settings & settings) {
    // dense_matrix<T, L> deb(*this);
    // vector<L>  deb_w(w);
    // deb.apply_from_left_to_X(deb_w, settings);
    // // cout << "deb" << endl;
    // // print_matrix(deb);
    // // cout << "w" << endl;
    // // print_vector(w.m_data);
    // // cout << "deb_w" << endl;
    // // print_vector(deb_w);
    vector<L> t(m_parent->dimension());
    for (unsigned i = 0; i < m_index_start; i++) {
        t[adjust_row_inverse(i)] = w[adjust_column_inverse(i)];
    }
    for (unsigned i = m_index_start; i < m_parent->dimension(); i++){
        t[adjust_row_inverse(i)] = row_by_vector_product(i, w);
    }
    for (unsigned i = 0; i < m_parent->dimension(); i++) {
        w[i] = t[i];
    }
#ifdef Z3DEBUG
    // cout << "w final" << endl;
    // print_vector(w.m_data);
    //  SASSERT(vectors_are_equal<L>(deb_w, w));
#endif
}

template <typename T, typename X>    bool square_dense_submatrix<T, X>::is_L_matrix() const {
#ifdef Z3DEBUG
    SASSERT(m_row_permutation.is_identity());
    for (unsigned i = 0; i < m_parent->dimension(); i++) {
        if (i < m_index_start) {
            SASSERT(m_column_permutation[i] == i);
            continue;
        }
        unsigned row_offs = (i-m_index_start)*m_dim;
        for (unsigned k = 0; k < m_dim; k++) {
            unsigned j = m_index_start + k;
            unsigned jex = adjust_column_inverse(j);
            if (jex > i) {
                SASSERT(is_zero(m_v[row_offs + k]));
            } else if (jex == i) {
                SASSERT(!is_zero(m_v[row_offs + k]));
            }
        }
    }
#endif
    return true;
}

template <typename T, typename X> void square_dense_submatrix<T, X>::apply_from_right(vector<T> & w) {
#ifdef Z3DEBUG
    // dense_matrix<T, X> deb(*this);
    // vector<T>  deb_w(w);
    // deb.apply_from_right(deb_w);
#endif
    vector<T> t(w.size());

    for (unsigned j = 0; j < m_index_start; j++) {
        t[adjust_column_inverse(j)] = w[adjust_row_inverse(j)];
    }
    unsigned end = m_index_start + m_dim;
    for (unsigned j = end; j < m_parent->dimension(); j++) {
        t[adjust_column_inverse(j)] = w[adjust_row_inverse(j)];
    }
    for (unsigned j = m_index_start; j < end; j++) {
        t[adjust_column_inverse(j)] = column_by_vector_product(j, w);
    }
    w = t;
#ifdef Z3DEBUG
    //  SASSERT(vector_are_equal<T>(deb_w, w));
#endif
}




#ifdef Z3DEBUG

template <typename T, typename X>    T square_dense_submatrix<T, X>::get_elem (unsigned i, unsigned j) const {
    i = adjust_row(i);
    j = adjust_column(j);
    if (i < m_index_start || j < m_index_start)
        return i == j? one_of_type<T>() : zero_of_type<T>();
    unsigned offs = (i - m_index_start)* m_dim + j - m_index_start;
    return  m_v[offs];
}

#endif
template <typename T, typename X> void square_dense_submatrix<T, X>::conjugate_by_permutation(permutation_matrix<T, X> & q) {
    m_row_permutation.multiply_by_permutation_from_left(q);
    m_column_permutation.multiply_by_reverse_from_right(q);
}
}
