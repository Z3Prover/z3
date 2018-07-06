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
#include "util/lp/tail_matrix.h"
#include "util/lp/permutation_matrix.h"
namespace lp {

// This is the sum of a unit matrix and a one-column matrix
template <typename T, typename X>
class eta_matrix
    : public tail_matrix<T, X> {
#ifdef Z3DEBUG
    unsigned m_length;
#endif
    unsigned m_column_index;
public:
    sparse_vector<T> m_column_vector;
    T m_diagonal_element;
#ifdef Z3DEBUG
    eta_matrix(unsigned column_index, unsigned length):
#else
        eta_matrix(unsigned column_index):
#endif

#ifdef Z3DEBUG
        m_length(length),
#endif
        m_column_index(column_index) {}

    bool is_dense() const override { return false; }

    void print(std::ostream & out) {
        print_matrix(*this, out);
    }

    bool is_unit() {
        return m_column_vector.size() == 0 && m_diagonal_element == 1;
    }

    bool set_diagonal_element(T const & diagonal_element) {
        m_diagonal_element = diagonal_element;
        return !lp_settings::is_eps_small_general(diagonal_element, 1e-12);
    }

    const T & get_diagonal_element() const {
        return m_diagonal_element;
    }

    void apply_from_left(vector<X> & w, lp_settings & ) override;

    template <typename L>
    void apply_from_left_local(indexed_vector<L> & w, lp_settings & settings);

    void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) override {
        apply_from_left_local(w, settings);
    }


    void push_back(unsigned row_index, T val ) {
        lp_assert(row_index != m_column_index);
        m_column_vector.push_back(row_index, val);
    }

    void apply_from_right(vector<T> & w) override;
    void apply_from_right(indexed_vector<T> & w) override;

#ifdef Z3DEBUG
    T get_elem(unsigned i, unsigned j) const override;
    unsigned row_count() const override { return m_length; }
    unsigned column_count() const override { return m_length; }
    void set_number_of_rows(unsigned m) override { m_length = m; }
    void set_number_of_columns(unsigned n) override { m_length = n; }
#endif
    void divide_by_diagonal_element() {
        m_column_vector.divide(m_diagonal_element);
    }
    void conjugate_by_permutation(permutation_matrix<T, X> & p);
};
}
