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
namespace lp {
template <typename B> class incremental_vector {
    vector<unsigned> m_stack_of_vector_sizes;
    vector<B> m_vector;
public:
    const B & operator[](unsigned a) const {
        return m_vector[a];
    }

    unsigned size() const {
        return m_vector.size();
    }
    
    void push_scope() {
        m_stack_of_vector_sizes.push_back(m_vector.size());
    }

    void pop_scope() {
        pop_scope(1);
    }

    template <typename T>  
    void pop_tail(vector<T> & v, unsigned k) {
        lp_assert(v.size() >= k);
        v.shrink(v.size() - k);
    }

    template <typename T>  
    void resize(vector<T> & v, unsigned new_size) {
        v.resize(new_size);
    }

    void pop_scope(unsigned k) {
        lp_assert(m_stack_of_vector_sizes.size() >= k);
        lp_assert(k > 0);
        m_vector.shrink(peek_size(k));
        unsigned new_st_size = m_stack_of_vector_sizes.size() - k;
        m_stack_of_vector_sizes.shrink(new_st_size);
    }

    void push_back(const B & b) {
        m_vector.push_back(b);
    }

    unsigned peek_size(unsigned k) const {
        lp_assert(k > 0 && k <= m_stack_of_vector_sizes.size());
        return m_stack_of_vector_sizes[m_stack_of_vector_sizes.size() - k];
    }
};
}

