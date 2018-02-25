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
#ifdef Z3DEBUG
#include "util/vector.h"
#include "util/lp/matrix.h"
namespace lp {
// used for debugging purposes only
template <typename T, typename X>
class dense_matrix: public matrix<T, X> {
public:
    struct ref {
        unsigned m_i;
        dense_matrix & m_s;
        ref(unsigned i, dense_matrix & s) :m_i(i * s.m_n), m_s(s){}
        T & operator[] (unsigned j) {
            return m_s.m_values[m_i + j];
        }
        const T & operator[] (unsigned j) const {
            return m_s.m_v[m_i + j];
        }
    };
    ref operator[] (unsigned i) {
        return ref(i, *this);
    }
    unsigned m_m; // number of rows
    unsigned m_n; // number of const
    vector<T> m_values;
    dense_matrix(unsigned m, unsigned n);

    dense_matrix operator*=(matrix<T, X> const & a) {
        SASSERT(column_count() == a.row_count());
        dense_matrix c(row_count(), a.column_count());
        for (unsigned i = 0; i < row_count(); i++) {
            for (unsigned j = 0; j < a.column_count(); j++) {
                T v = numeric_traits<T>::zero();
                for (unsigned k = 0; k < a.column_count(); k++) {
                    v += get_elem(i, k) * a(k, j);
                }
                c.set_elem(i, j, v);
            }
        }
        *this = c;
        return *this;
    }

    dense_matrix & operator=(matrix<T, X> const & other);

    dense_matrix & operator=(dense_matrix const & other);

    dense_matrix(matrix<T, X> const * other);
    void apply_from_right(T * w);

    void apply_from_right(vector <T> & w);

    T * apply_from_left_with_different_dims(vector<T> &  w);
    void apply_from_left(vector<T> & w , lp_settings & ) { apply_from_left(w); }

    void apply_from_left(vector<T> & w);

    void apply_from_left(X * w, lp_settings & );

    void apply_from_left_to_X(vector<X> & w, lp_settings & );

    void set_number_of_rows(unsigned /*m*/) override {}
    void set_number_of_columns(unsigned /*n*/) override {}
#ifdef Z3DEBUG
    T get_elem(unsigned i, unsigned j) const override { return m_values[i * m_n + j]; }
#endif

    unsigned row_count() const override { return m_m; }
    unsigned column_count() const override { return m_n; }

    void set_elem(unsigned i, unsigned j, const T& val) {  m_values[i * m_n + j] = val;  }

    // This method pivots row i to row i0 by muliplying row i by
    //   alpha and adding it to row i0.
    void pivot_row_to_row(unsigned i, const T& alpha, unsigned i0,
                          const double & pivot_epsilon);

    void swap_columns(unsigned a, unsigned b);

    void swap_rows(unsigned a, unsigned b);

    void multiply_row_by_constant(unsigned row, T & t);

};
template <typename T, typename X>
dense_matrix<T, X> operator* (matrix<T, X> & a, matrix<T, X> & b);
}
#endif
