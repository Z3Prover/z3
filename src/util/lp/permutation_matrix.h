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
#include <algorithm>
#include "util/debug.h"
#include <string>
#include "util/lp/sparse_vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/lp_settings.h"
#include "util/lp/matrix.h"
#include "util/lp/tail_matrix.h"
namespace lp {
#ifdef Z3DEBUG
    inline bool is_even(int k) {  return (k/2)*2 == k; }
#endif

    template <typename T, typename X>
class permutation_matrix : public tail_matrix<T, X> {
        vector<unsigned> m_permutation;
        vector<unsigned> m_rev;
        vector<unsigned> m_work_array;
        vector<T> m_T_buffer;
        vector<X> m_X_buffer;


        class ref {
            permutation_matrix & m_p;
            unsigned m_i;
        public:
            ref(permutation_matrix & m, unsigned i):m_p(m), m_i(i) {}

            ref & operator=(unsigned  v) { m_p.set_val(m_i, v); return *this; }

            ref & operator=(ref const & v) {
                m_p.set_val(m_i, v.m_p.m_permutation[v.m_i]);
                return *this;
            }
            operator unsigned & () const { return m_p.m_permutation[m_i]; }
        };

    public:
        permutation_matrix() {}
        permutation_matrix(unsigned length);

        permutation_matrix(unsigned length, vector<unsigned> const & values);
        // create a unit permutation of the given length
        void init(unsigned length);
        unsigned get_rev(unsigned i) { return m_rev[i]; }
        bool is_dense() const override { return false; }
#ifdef Z3DEBUG
        permutation_matrix get_inverse() const {
            return permutation_matrix(size(), m_rev);
        }
        void print(std::ostream & out) const;
#endif

        ref operator[](unsigned i) { return ref(*this, i); }

        unsigned operator[](unsigned i) const { return m_permutation[i]; }

        void apply_from_left(vector<X> & w, lp_settings &) override;

        void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) override;

        void apply_from_right(vector<T> & w) override;

        void apply_from_right(indexed_vector<T> & w) override;
        
        template <typename L>
        void copy_aside(vector<L> & t, vector<unsigned> & tmp_index, indexed_vector<L> & w);

        template <typename L>
        void clear_data(indexed_vector<L> & w);

        template <typename L>
        void apply_reverse_from_left(indexed_vector<L> & w);

        void apply_reverse_from_left_to_T(vector<T> & w);
        void apply_reverse_from_left_to_X(vector<X> & w);

        void apply_reverse_from_right_to_T(vector<T> & w);
        void apply_reverse_from_right_to_T(indexed_vector<T> & w);
        void apply_reverse_from_right_to_X(vector<X> & w);

        void set_val(unsigned i, unsigned pi) {
            SASSERT(i < size() && pi < size());  m_permutation[i] = pi;  m_rev[pi] = i;  }

        void transpose_from_left(unsigned i, unsigned j);

        unsigned apply_reverse(unsigned i) const { return m_rev[i];  }

        void transpose_from_right(unsigned i, unsigned j);
#ifdef Z3DEBUG
        T get_elem(unsigned i, unsigned j) const override {
            return m_permutation[i] == j? numeric_traits<T>::one() : numeric_traits<T>::zero();
        }
        unsigned row_count() const override { return size(); }
        unsigned column_count() const override { return size(); }
        void set_number_of_rows(unsigned /*m*/) override { }
        void set_number_of_columns(unsigned /*n*/) override { }
#endif
        void multiply_by_permutation_from_left(permutation_matrix<T, X> & p);

        // this is multiplication in the matrix sense
        void multiply_by_permutation_from_right(permutation_matrix<T, X> & p);

        void multiply_by_reverse_from_right(permutation_matrix<T, X> & q);

        void multiply_by_permutation_reverse_from_left(permutation_matrix<T, X> & r);

        void shrink_by_one_identity();

        bool is_identity() const;

        unsigned size() const { return static_cast<unsigned>(m_rev.size()); }

        unsigned * values() const { return m_permutation.c_ptr(); }

        void resize(unsigned size) {
            unsigned old_size = m_permutation.size();
            m_permutation.resize(size);
            m_rev.resize(size);
            m_T_buffer.resize(size);
            m_X_buffer.resize(size);
            for (unsigned i = old_size; i < size; i++) {
                m_permutation[i] = m_rev[i] = i;
    }
        }
        
    }; // end of the permutation class

}
