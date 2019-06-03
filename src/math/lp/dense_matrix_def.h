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
#include "math/lp/lp_settings.h"
#ifdef Z3DEBUG
#include "util/vector.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/dense_matrix.h"
namespace lp {
template <typename T, typename X> dense_matrix<T, X>::dense_matrix(unsigned m, unsigned n) : m_m(m), m_n(n), m_values(m * n, numeric_traits<T>::zero()) {
}

template <typename T, typename X> dense_matrix<T, X>&
dense_matrix<T, X>::operator=(matrix<T, X> const & other){
    if ( this == & other)
        return *this;
    m_values = new T[m_m * m_n];
    for (unsigned i = 0; i < m_m; i ++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other.get_elem(i, j);
    return *this;
}

template <typename T, typename X> dense_matrix<T, X>&
dense_matrix<T, X>::operator=(dense_matrix const & other){
    if ( this == & other)
        return *this;
    m_m = other.m_m;
    m_n = other.m_n;
    m_values.resize(m_m * m_n);
    for (unsigned i = 0; i < m_m; i ++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other.get_elem(i, j);
    return *this;
}

template <typename T, typename X> dense_matrix<T, X>::dense_matrix(matrix<T, X> const * other) :
    m_m(other->row_count()),
    m_n(other->column_count()) {
    m_values.resize(m_m*m_n);
    for (unsigned i = 0; i < m_m; i++)
        for (unsigned j = 0; j < m_n; j++)
            m_values[i * m_n + j] = other->get_elem(i, j);
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_right(T * w) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(j, i);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i++) {
        w[i] = t[i];
    }
    delete [] t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_right(vector <T> & w) {
    vector<T> t(m_m, numeric_traits<T>::zero());
    for (unsigned i = 0; i < m_m; i ++) {
        auto & v = t[i];
        for (unsigned j = 0; j < m_m; j++)
            v += w[j]* get_elem(j, i);
    }

    for (unsigned i = 0; i < m_m; i++)
        w[i] = t[i];
}

template <typename T, typename X> T* dense_matrix<T, X>::
apply_from_left_with_different_dims(vector<T> &  w) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_n; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    return t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_left(vector<T> & w) {
    T * t = new T[m_m];
    for (unsigned i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (unsigned j = 0; j < m_m; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    for (unsigned i = 0; i < m_m; i ++) {
        w[i] = t[i];
    }
    delete [] t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_left(X * w, lp_settings & ) {
    T * t = new T[m_m];
    for (int i = 0; i < m_m; i ++) {
        T v = numeric_traits<T>::zero();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i ++) {
        w[i] = t[i];
    }
    delete [] t;
}

template <typename T, typename X> void dense_matrix<T, X>::apply_from_left_to_X(vector<X> & w, lp_settings & ) {
    vector<X> t(m_m);
    for (int i = 0; i < m_m; i ++) {
        X v = zero_of_type<X>();
        for (int j = 0; j < m_m; j++) {
            v += w[j]* get_elem(i, j);
        }
        t[i] = v;
    }

    for (int i = 0; i < m_m; i ++) {
        w[i] = t[i];
    }
}

// This method pivots row i to row i0 by muliplying row i by
//   alpha and adding it to row i0.
template <typename T, typename X> void dense_matrix<T, X>::pivot_row_to_row(unsigned i, const T& alpha, unsigned i0,
                                                                            const double & pivot_epsilon) {
    for (unsigned j = 0; j < m_n; j++) {
        m_values[i0 * m_n + j] += m_values[i * m_n + j] * alpha;
        if (fabs(m_values[i0 + m_n + j]) < pivot_epsilon) {
            m_values[i0 + m_n + j] = numeric_traits<T>::zero();;
        }
    }
}

template <typename T, typename X> void dense_matrix<T, X>::swap_columns(unsigned a, unsigned b) {
    for (unsigned i = 0; i < m_m; i++) {
        T t = get_elem(i, a);
        set_elem(i, a, get_elem(i, b));
        set_elem(i, b, t);
    }
}

template <typename T, typename X> void dense_matrix<T, X>::swap_rows(unsigned a, unsigned b) {
    for (unsigned i = 0; i < m_n; i++) {
        T t = get_elem(a, i);
        set_elem(a, i, get_elem(b, i));
        set_elem(b, i, t);
    }
}

template <typename T, typename X> void dense_matrix<T, X>::multiply_row_by_constant(unsigned row, T & t) {
    for (unsigned i = 0; i < m_n; i++) {
        set_elem(row, i, t * get_elem(row, i));
    }
}

template <typename T, typename X>
dense_matrix<T, X> operator* (matrix<T, X> & a, matrix<T, X> & b){
    lp_assert(a.column_count() == b.row_count());
    dense_matrix<T, X> ret(a.row_count(), b.column_count());
    for (unsigned i = 0; i < ret.m_m; i++)
        for (unsigned j = 0; j< ret.m_n; j++) {
            T v = numeric_traits<T>::zero();
            for (unsigned k = 0; k < a.column_count(); k ++){
                v += (a.get_elem(i, k) * b.get_elem(k, j));
            }
            ret.set_elem(i, j, v);
        }
    return  ret;
}
}
#endif
