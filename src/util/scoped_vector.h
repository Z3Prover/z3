/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    scoped_vector.h

Abstract:

    Vector that restores during backtracking.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-13

Revision History:

--*/
#ifndef SCOPED_VECTOR_H_
#define SCOPED_VECTOR_H_

#include"vector.h"

template<typename T>
class scoped_vector {
    unsigned         m_size;
    unsigned         m_elems_start;
    unsigned_vector  m_sizes;
    vector<T>        m_elems;
    unsigned_vector  m_elems_lim;
    unsigned_vector  m_index;
    unsigned_vector  m_src, m_dst;
    unsigned_vector  m_src_lim;
public:
    scoped_vector(): m_size(0), m_elems_start(0) {}

    // m_index : External-Index -> Internal-Index
    // m_index.size() = max(m_sizes)
    // m_src[i] -> m_dst[i] // trail into m_index updates
    // m_src_lim last index to be updated.
    
    void push_scope() {
        m_elems_start = m_elems.size();
        m_sizes.push_back(m_size);        
        m_src_lim.push_back(m_src.size());
        m_elems_lim.push_back(m_elems_start);
    }

    void pop_scopes(unsigned num_scopes) {
        if (num_scopes == 0) return;
        unsigned new_size = m_sizes.size() - num_scopes;
        unsigned src_lim = m_src_lim[new_size];

        for (unsigned i = m_src.size(); i > src_lim; ) {
            --i;
            m_index[m_src[i]] = m_dst[i];
        }
        m_src.shrink(src_lim);
        m_dst.shrink(src_lim);
        m_src_lim.shrink(new_size);

        m_elems.shrink(m_elems_lim[new_size]);
        m_elems_lim.resize(new_size);
        m_elems_start = m_elems.size();

        m_size = m_sizes[new_size];
        m_sizes.shrink(new_size);
    }

    T const& operator[](unsigned idx) const {
        SASSERT(idx < m_size);
        return m_elems[m_index[idx]];
    }

    void set(unsigned idx, T const& t) {
        SASSERT(idx < m_size);
        unsigned n = m_index[idx];
        if (n >= m_elems_start) {
            m_elems[n] = t;
        }
        else {
            set_index(idx, m_elems.size());
            m_elems.push_back(t);
        }
        SASSERT(invariant());
    }

    void push_back(T const& t) {
        set_index(m_size, m_elems.size());
        m_elems.push_back(t);    
        ++m_size;
        SASSERT(invariant());
    }

    void pop_back() {
        SASSERT(m_size > 0);
        if (m_index[m_size-1] == m_elems.size()-1 && 
            m_elems.size() > m_elems_start) {
            m_elems.pop_back();
        }
        --m_size;
        SASSERT(invariant());
    }

    unsigned size() const { return m_size; }
    
    bool empty() const { return m_size == 0; }

private:
    void set_index(unsigned src, unsigned dst) {
        while (src >= m_index.size()) {
            m_index.push_back(0);
        }
        SASSERT(src < m_index.size());
        if (src < m_elems_start) {
            m_src.push_back(src);
            m_dst.push_back(m_index[src]);
        }
        m_index[src] = dst;
    }

    bool invariant() const {
        return 
            m_size <= m_elems.size() &&
            m_elems_start <= m_elems.size();
    }
};

#endif
