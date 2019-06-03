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
#include "util/debug.h"
#include <string>
#include "math/lp/sparse_vector.h"
#include "math/lp/indexed_vector.h"
#include "math/lp/permutation_matrix.h"
namespace lp {
    // This is the sum of a unit matrix and a lower triangular matrix
    // with non-zero elements only in one row
template <typename T, typename X>
class row_eta_matrix
        : public tail_matrix<T, X> {
#ifdef Z3DEBUG
    unsigned m_dimension;
#endif
    unsigned m_row_start;
    unsigned m_row;
    sparse_vector<T> m_row_vector;
public:
#ifdef Z3DEBUG
    row_eta_matrix(unsigned row_start, unsigned row, unsigned dim):
#else
    row_eta_matrix(unsigned row_start, unsigned row):
#endif

#ifdef Z3DEBUG
    m_dimension(dim),
#endif
    m_row_start(row_start), m_row(row) {
    }

    bool is_dense() const override { return false; }

    void print(std::ostream & out) {
        print_matrix(*this, out);
    }

    const T & get_diagonal_element() const {
        return m_row_vector.m_data[m_row];
    }

    void apply_from_left(vector<X> & w, lp_settings &) override;

    void apply_from_left_local_to_T(indexed_vector<T> & w, lp_settings & settings);
    void apply_from_left_local_to_X(indexed_vector<X> & w, lp_settings & settings);

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) override {
        apply_from_left_local_to_T(w, settings);
    }

    void push_back(unsigned row_index, T val ) {
        lp_assert(row_index != m_row);
        m_row_vector.push_back(row_index, val);
    }

    void apply_from_right(vector<T> & w) override;
    void apply_from_right(indexed_vector<T> & w) override;

    void conjugate_by_permutation(permutation_matrix<T, X> & p);
#ifdef Z3DEBUG
    T get_elem(unsigned row, unsigned col) const override;
    unsigned row_count() const override { return m_dimension; }
    unsigned column_count() const override { return m_dimension; }
    void set_number_of_rows(unsigned m) override { m_dimension = m; }
    void set_number_of_columns(unsigned n) override { m_dimension = n; }
#endif
}; // end of row_eta_matrix
}
