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
#include "math/lp/indexed_vector.h"
#include "math/lp/lp_settings.h"
#include "math/lp/matrix.h"
namespace lp {

template <typename T, typename X>
class permutation_matrix 
#ifdef Z3DEBUG
    : public matrix<T, X>
#endif 
{
        vector<unsigned> m_permutation;
        vector<unsigned> m_rev;

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
        permutation_matrix() = default;
        permutation_matrix(unsigned length);

        permutation_matrix(unsigned length, vector<unsigned> const & values);
        // create a unit permutation of the given length
        void init(unsigned length);
        unsigned get_rev(unsigned i) { return m_rev[i]; }

#ifdef Z3DEBUG        
        void print(std::ostream & out) const;
#endif

        ref operator[](unsigned i) { return ref(*this, i); }

        unsigned operator[](unsigned i) const { return m_permutation[i]; }
        
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

        unsigned size() const { return static_cast<unsigned>(m_rev.size()); }

        void resize(unsigned size) {
            unsigned old_size = m_permutation.size();
            m_permutation.resize(size);
            m_rev.resize(size);
            for (unsigned i = old_size; i < size; i++) {
                m_permutation[i] = m_rev[i] = i;
    }
        }
        
    }; // end of the permutation class

}
