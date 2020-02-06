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
#include "util/vector.h"
#include "math/lp/permutation_matrix.h"
#include <unordered_map>
#include "math/lp/static_matrix.h"
#include <set>
#include <utility>
#include <string>
#include <algorithm>
#include <queue>
#include "math/lp/indexed_value.h"
#include "math/lp/indexed_vector.h"
#include <functional>
#include "math/lp/lp_settings.h"
#include "math/lp/eta_matrix.h"
#include "math/lp/binary_heap_upair_queue.h"
#include "math/lp/square_sparse_matrix.h"
namespace lp {
template <typename T, typename X>
class square_dense_submatrix : public tail_matrix<T, X> {
    // the submatrix uses the permutations of the parent matrix to access the elements
    struct ref {
        unsigned m_i_offset;
        square_dense_submatrix & m_s;
        ref(unsigned i, square_dense_submatrix & s) :
            m_i_offset((i - s.m_index_start) * s.m_dim), m_s(s){}
        T & operator[] (unsigned j) {
            lp_assert(j >= m_s.m_index_start);
            return m_s.m_v[m_i_offset + m_s.adjust_column(j) - m_s.m_index_start];
        }
        const T & operator[] (unsigned j) const {
            lp_assert(j >= m_s.m_index_start);
            return m_s.m_v[m_i_offset + m_s.adjust_column(j) - m_s.m_index_start];
        }
    };
public:
    unsigned m_index_start;
    unsigned m_dim;
    vector<T> m_v;
    square_sparse_matrix<T, X> * m_parent;
    permutation_matrix<T, X>  m_row_permutation;
    indexed_vector<T> m_work_vector;
public:
    permutation_matrix<T, X>  m_column_permutation;
    bool is_active() const { return m_parent != nullptr; }

    square_dense_submatrix() {}

    square_dense_submatrix (square_sparse_matrix<T, X> *parent_matrix, unsigned index_start);

    void init(square_sparse_matrix<T, X> *parent_matrix, unsigned index_start);

    bool is_dense() const override { return true; }
    
    ref operator[] (unsigned i) {
        lp_assert(i >= m_index_start);
        lp_assert(i < m_parent->dimension());
        return ref(i, *this);
    }

    int find_pivot_column_in_row(unsigned i) const;

    void swap_columns(unsigned i, unsigned j) {
        if (i != j)
            m_column_permutation.transpose_from_left(i, j);
    }

    unsigned adjust_column(unsigned  col)  const{
        if (col >= m_column_permutation.size())
            return col;
        return m_column_permutation.apply_reverse(col);
    }

    unsigned adjust_column_inverse(unsigned  col)  const{
        if (col >= m_column_permutation.size())
            return col;
        return m_column_permutation[col];
    }
    unsigned adjust_row(unsigned row)  const{
        if (row >= m_row_permutation.size())
            return row;
        return m_row_permutation[row];
    }

    unsigned adjust_row_inverse(unsigned row)  const{
        if (row >= m_row_permutation.size())
            return row;
        return m_row_permutation.apply_reverse(row);
    }

    void pivot(unsigned i, lp_settings & settings);

    void pivot_row_to_row(unsigned i, unsigned row, lp_settings & settings);;

    void divide_row_by_pivot(unsigned i);

    void update_parent_matrix(lp_settings & settings);

    void update_existing_or_delete_in_parent_matrix_for_row(unsigned i, lp_settings & settings);

    void push_new_elements_to_parent_matrix(lp_settings & settings);

    template <typename L>
    L row_by_vector_product(unsigned i, const vector<L> & v);

    template <typename L>
    L column_by_vector_product(unsigned j, const vector<L> & v);

    template <typename L>
    L row_by_indexed_vector_product(unsigned i, const indexed_vector<L> & v);

    template <typename L>
    void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings);

    template <typename L>
    void apply_from_left_to_vector(vector<L> & w);

    bool is_L_matrix() const;

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) override {
        apply_from_left_local(w, settings);
    }

    
    
    void apply_from_right(indexed_vector<T> & w) override {
#if 1==0
        indexed_vector<T> wcopy = w;
        apply_from_right(wcopy.m_data);
        wcopy.m_index.clear();
        if (numeric_traits<T>::precise()) {
            for (unsigned i = 0; i < m_parent->dimension(); i++) {
                if (!is_zero(wcopy.m_data[i]))
                    wcopy.m_index.push_back(i);
            }
        } else  {
            for (unsigned i = 0; i < m_parent->dimension(); i++) {
                T & v = wcopy.m_data[i];
                if (!lp_settings::is_eps_small_general(v, 1e-14)){
                    wcopy.m_index.push_back(i);
                } else {
                    v = zero_of_type<T>();
                }
            }
        }
        lp_assert(wcopy.is_OK());
        apply_from_right(w.m_data);
        w.m_index.clear();
        if (numeric_traits<T>::precise()) {
            for (unsigned i = 0; i < m_parent->dimension(); i++) {
                if (!is_zero(w.m_data[i]))
                    w.m_index.push_back(i);
            }
        } else  {
            for (unsigned i = 0; i < m_parent->dimension(); i++) {
                T & v = w.m_data[i];
                if (!lp_settings::is_eps_small_general(v, 1e-14)){
                    w.m_index.push_back(i);
                } else {
                    v = zero_of_type<T>();
                }
            }
        }
#else
        lp_assert(w.is_OK());
        lp_assert(m_work_vector.is_OK());
        m_work_vector.resize(w.data_size());
        m_work_vector.clear();
        lp_assert(m_work_vector.is_OK());
        unsigned end = m_index_start + m_dim;
        for (unsigned k : w.m_index) {
            // find j such that k = adjust_row_inverse(j)
            unsigned j = adjust_row(k);
            if (j < m_index_start || j >= end) {
                m_work_vector.set_value(w[k], adjust_column_inverse(j));
            }  else { // j >= m_index_start and j < end
                unsigned offset = (j - m_index_start) * m_dim; // this is the row start
                const T& wv = w[k];
                for (unsigned col = m_index_start; col < end; col++, offset ++) {
                    unsigned adj_col =  adjust_column_inverse(col);
                    m_work_vector.add_value_at_index(adj_col, m_v[offset] * wv);
                }
            }
        }
        m_work_vector.clean_up();
        lp_assert(m_work_vector.is_OK());
        w = m_work_vector;
#endif
    }
    void apply_from_left(vector<X> & w, lp_settings & /*settings*/) override {
        apply_from_left_to_vector(w);// , settings);
    }

    void apply_from_right(vector<T> & w) override;

#ifdef Z3DEBUG
    T get_elem (unsigned i, unsigned j) const override;
    unsigned row_count() const override { return m_parent->row_count();}
    unsigned column_count() const override { return row_count();}
    void set_number_of_rows(unsigned) override {}
    void set_number_of_columns(unsigned) override {}
#endif
    void conjugate_by_permutation(permutation_matrix<T, X> & q);
};
}
