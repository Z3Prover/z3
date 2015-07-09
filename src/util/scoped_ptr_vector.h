/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_ptr_vector.h

Abstract:

    Basic template of scoped ptrs.
    TODO: improve

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#ifndef SCOPED_PTR_VECTOR_H_
#define SCOPED_PTR_VECTOR_H_

#include"vector.h"
#include"util.h"

template<typename T>
class scoped_ptr_vector {
    ptr_vector<T> m_vector;
public:
    ~scoped_ptr_vector() { reset(); }
    void reset() { std::for_each(m_vector.begin(), m_vector.end(), delete_proc<T>()); m_vector.reset(); }
    void push_back(T * ptr) { m_vector.push_back(ptr); }
    T * operator[](unsigned idx) const { return m_vector[idx]; }
    void set(unsigned idx, T * ptr) { 
        if (m_vector[idx] == ptr) 
            return; 
        dealloc(m_vector[idx]); 
        m_vector[idx] = ptr; 
    }
    unsigned size() const { return m_vector.size(); }
    bool empty() const { return m_vector.empty(); }
    void resize(unsigned sz) { 
        if (sz < m_vector.size()) {
            for (unsigned i = m_vector.size(); i < sz; i++)
                dealloc(m_vector[i]);
            m_vector.shrink(sz); 
        }
        else {
            for (unsigned i = m_vector.size(); i < sz; i++)
                push_back(0);
        }
    }
};

#endif
