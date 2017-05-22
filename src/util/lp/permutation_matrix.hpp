/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/vector.h"
#include "util/lp/permutation_matrix.h"
namespace lean {
template <typename T, typename X> permutation_matrix<T, X>::permutation_matrix(unsigned length): m_permutation(length), m_rev(length), m_T_buffer(length), m_X_buffer(length)  {
    for (unsigned i = 0; i < length; i++) { // do not change the direction of the loop because of the vectorization bug in clang3.3
        m_permutation[i] = m_rev[i] = i;
    }
}

template <typename T, typename X> permutation_matrix<T, X>::permutation_matrix(unsigned length, vector<unsigned> const & values): m_permutation(length), m_rev(length) , m_T_buffer(length), m_X_buffer(length) {
    for (unsigned i = 0; i < length; i++) {
        set_val(i, values[i]);
    }
}
// create a unit permutation of the given length
template <typename T, typename X> void permutation_matrix<T, X>::init(unsigned length) {
    m_permutation.resize(length);
    m_rev.resize(length);
    m_T_buffer.resize(length);
    m_X_buffer.resize(length);
    for (unsigned i = 0; i < length; i++) {
        m_permutation[i] = m_rev[i] = i;
    }
}

#ifdef LEAN_DEBUG
template <typename T, typename X> void permutation_matrix<T, X>::print(std::ostream & out) const {
    out << "[";
    for (unsigned i = 0; i < size(); i++) {
        out << m_permutation[i];
        if (i < size() - 1) {
            out << ",";
        } else {
            out << "]";
        }
    }
    out << std::endl;
}
#endif

template <typename T, typename X>
void permutation_matrix<T, X>::apply_from_left(vector<X> & w, lp_settings & ) {
#ifdef LEAN_DEBUG
    // dense_matrix<L, X> deb(*this);
    // L * deb_w = clone_vector<L>(w, row_count());
    // deb.apply_from_left(deb_w);
#endif
    // std::cout << " apply_from_left " << std::endl;
    lean_assert(m_X_buffer.size() == w.size());
    unsigned i = size();
    while (i-- > 0) {
        m_X_buffer[i] = w[m_permutation[i]];
    }
    i = size();
    while (i-- > 0) {
        w[i] = m_X_buffer[i];
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<L>(deb_w, w, row_count()));
    // delete [] deb_w;
#endif
}

template <typename T, typename X>
void permutation_matrix<T, X>::apply_from_left_to_T(indexed_vector<T> & w, lp_settings & ) {
    vector<T> t(w.m_index.size());
    vector<unsigned> tmp_index(w.m_index.size());
    copy_aside(t, tmp_index, w); // todo: is it too much copying
    clear_data(w);
    // set the new values
    for (unsigned i = static_cast<unsigned>(t.size()); i > 0;) {
        i--;
        unsigned j = m_rev[tmp_index[i]];
        w[j] = t[i];
        w.m_index[i] = j;
    }
}

template <typename T, typename X> void permutation_matrix<T, X>::apply_from_right(vector<T> & w) {
#ifdef LEAN_DEBUG
    // dense_matrix<T, X> deb(*this);
    // T * deb_w = clone_vector<T>(w, row_count());
    // deb.apply_from_right(deb_w);
#endif
    lean_assert(m_T_buffer.size() == w.size());
    for (unsigned i = 0; i < size(); i++) {
        m_T_buffer[i] = w[m_rev[i]];
    }

    for (unsigned i = 0; i < size(); i++) {
        w[i] = m_T_buffer[i];
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<T>(deb_w, w, row_count()));
    // delete [] deb_w;
#endif
}

template <typename T, typename X> void permutation_matrix<T, X>::apply_from_right(indexed_vector<T> & w) {
#ifdef LEAN_DEBUG
    vector<T> wcopy(w.m_data);
    apply_from_right(wcopy);
#endif
    vector<T> buffer(w.m_index.size());
    vector<unsigned> index_copy(w.m_index);
    for (unsigned i = 0; i < w.m_index.size(); i++) {
        buffer[i] = w.m_data[w.m_index[i]];
    }
    w.clear();

    for (unsigned i = 0; i < index_copy.size(); i++) {
        unsigned j = index_copy[i];
        unsigned pj = m_permutation[j];
        w.set_value(buffer[i], pj);
    }
    lean_assert(w.is_OK());
#ifdef LEAN_DEBUG
    lean_assert(vectors_are_equal(wcopy, w.m_data));
#endif
}


template <typename T, typename X> template <typename L>
void permutation_matrix<T, X>::copy_aside(vector<L> & t, vector<unsigned> & tmp_index, indexed_vector<L> & w) {
    for (unsigned i = static_cast<unsigned>(t.size()); i > 0;) {
        i--;
        unsigned j = w.m_index[i];
        t[i] = w[j]; // copy aside all non-zeroes
        tmp_index[i] = j; // and the indices too
    }
}

template <typename T, typename X> template <typename L>
void permutation_matrix<T, X>::clear_data(indexed_vector<L> & w) {
    // clear old non-zeroes
    for (unsigned i = static_cast<unsigned>(w.m_index.size()); i > 0;) {
        i--;
        unsigned j = w.m_index[i];
        w[j] = zero_of_type<L>();
    }
}

template <typename T, typename X>template <typename L>
void permutation_matrix<T, X>::apply_reverse_from_left(indexed_vector<L> & w) {
    // the result will be w = p(-1) * w
#ifdef LEAN_DEBUG
    // dense_matrix<L, X> deb(get_reverse());
    // L * deb_w = clone_vector<L>(w.m_data, row_count());
    // deb.apply_from_left(deb_w);
#endif
    vector<L> t(w.m_index.size());
    vector<unsigned> tmp_index(w.m_index.size());

    copy_aside(t, tmp_index, w);
    clear_data(w);

    // set the new values
    for (unsigned i = static_cast<unsigned>(t.size()); i > 0;) {
        i--;
        unsigned j = m_permutation[tmp_index[i]];
        w[j] = t[i];
        w.m_index[i] = j;
    }
#ifdef LEAN_DEBUG
    // lean_assert(vectors_are_equal<L>(deb_w, w.m_data, row_count()));
    // delete [] deb_w;
#endif
}

template <typename T, typename X>
void permutation_matrix<T, X>::apply_reverse_from_left_to_T(vector<T> & w) {
    // the result will be w = p(-1) * w
    lean_assert(m_T_buffer.size() == w.size());
    unsigned i = size();
    while (i-- > 0) {
        m_T_buffer[m_permutation[i]] = w[i];
    }
    i = size();
    while (i-- > 0) {
        w[i] = m_T_buffer[i];
    }
}
template <typename T, typename X>
void permutation_matrix<T, X>::apply_reverse_from_left_to_X(vector<X> & w) {
    // the result will be w = p(-1) * w
    lean_assert(m_X_buffer.size() == w.size());
    unsigned i = size();
    while (i-- > 0) {
        m_X_buffer[m_permutation[i]] = w[i];
    }
    i = size();
    while (i-- > 0) {
        w[i] = m_X_buffer[i];
    }
}

template <typename T, typename X>
void permutation_matrix<T, X>::apply_reverse_from_right_to_T(vector<T> & w) {
    // the result will be w = w * p(-1)
    lean_assert(m_T_buffer.size() == w.size());
    unsigned i = size();
    while (i-- > 0) {
        m_T_buffer[i] = w[m_permutation[i]];
    }
    i = size();
    while (i-- > 0) {
        w[i] = m_T_buffer[i];
    }
}

template <typename T, typename X>
void permutation_matrix<T, X>::apply_reverse_from_right_to_T(indexed_vector<T> & w) {
    // the result will be w = w * p(-1)
#ifdef LEAN_DEBUG
    // vector<T> wcopy(w.m_data);
    // apply_reverse_from_right_to_T(wcopy);
#endif
    lean_assert(w.is_OK());
    vector<T> tmp;
    vector<unsigned> tmp_index(w.m_index);
    for (auto i : w.m_index) {
        tmp.push_back(w[i]);
    }
    w.clear();
    
    for (unsigned k = 0; k < tmp_index.size(); k++) {
        unsigned j = tmp_index[k];
        w.set_value(tmp[k], m_rev[j]);
    }

    // lean_assert(w.is_OK());    
    // lean_assert(vectors_are_equal(w.m_data, wcopy));
}


template <typename T, typename X>
void permutation_matrix<T, X>::apply_reverse_from_right_to_X(vector<X> & w) {
    // the result will be w = w * p(-1)
    lean_assert(m_X_buffer.size() == w.size());
    unsigned i = size();
    while (i-- > 0) {
        m_X_buffer[i] = w[m_permutation[i]];
    }
    i = size();
    while (i-- > 0) {
        w[i] = m_X_buffer[i];
    }
}

template <typename T, typename X> void permutation_matrix<T, X>::transpose_from_left(unsigned i, unsigned j) {
    // the result will be this = (i,j)*this
    lean_assert(i < size() && j < size() && i != j);
    auto pi = m_rev[i];
    auto pj = m_rev[j];
    set_val(pi, j);
    set_val(pj, i);
}

template <typename T, typename X> void permutation_matrix<T, X>::transpose_from_right(unsigned i, unsigned j) {
    // the result will be this = this * (i,j)
    lean_assert(i < size() && j < size() && i != j);
    auto pi = m_permutation[i];
    auto pj = m_permutation[j];
    set_val(i, pj);
    set_val(j, pi);
}

template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_permutation_from_left(permutation_matrix<T, X> & p) {
    m_work_array = m_permutation;
    lean_assert(p.size() == size());
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, m_work_array[p[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
    }
}

// this is multiplication in the matrix sense
template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_permutation_from_right(permutation_matrix<T, X> & p) {
    m_work_array = m_permutation;
    lean_assert(p.size() == size());
    unsigned i = size();
    while (i-- > 0)
        set_val(i, p[m_work_array[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
    
}

template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_reverse_from_right(permutation_matrix<T, X> & q){ // todo : condensed permutations ?
    lean_assert(q.size() == size());
    m_work_array = m_permutation;
    // the result is this = this*q(-1)
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, q.m_rev[m_work_array[i]]); // we have m(P)*m(Q) = m(QP), where m is the matrix of the permutation
    }
}

template <typename T, typename X> void permutation_matrix<T, X>::multiply_by_permutation_reverse_from_left(permutation_matrix<T, X> & r){ // todo : condensed permutations?
    // the result is this = r(-1)*this
    m_work_array = m_permutation;
    // the result is this = this*q(-1)
    unsigned i = size();
    while (i-- > 0) {
        set_val(i, m_work_array[r.m_rev[i]]);
    }
}


template <typename T, typename X> bool permutation_matrix<T, X>::is_identity() const {
    unsigned i = size();
    while (i-- > 0) {
        if (m_permutation[i] != i) {
            return false;
        }
    }
    return true;
}


}
