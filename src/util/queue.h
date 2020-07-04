/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    queue.h

Abstract:
   
    Generic queue.

Author:

    Nikolaj Bjorner (nbjorner) 2017-4-17

Notes:

--*/
#pragma once

#include "vector.h"

template<class T>
class queue {
    vector<T> m_elems;
    unsigned  m_head;
    unsigned  m_capacity;
    
public:
    
    queue(): m_head(0), m_capacity(0) {}

    void push(T const& t) { m_elems.push_back(t); }

    bool empty() const { 
        return m_head == m_elems.size(); 
    }

    T top() const {
        return m_elems[m_head];
    }

    T pop_front() { 
        SASSERT(!empty());
        m_capacity = std::max(m_capacity, m_elems.size());
        SASSERT(m_head < m_elems.size()); 
        if (2 * m_head > m_capacity && m_capacity > 10) {
            for (unsigned i = 0; i < m_elems.size() - m_head; ++i) {
                m_elems[i] = m_elems[i + m_head];
            }
            m_elems.shrink(m_elems.size() - m_head);
            m_head = 0;
        } 
        return m_elems[m_head++];        
    }


    T back() const {
        return m_elems[m_elems.size() - 1];
    }

    T pop_back() {
        SASSERT(!empty());
        SASSERT(m_head < m_elems.size()); 
        T result = back();
        m_elems.shrink(m_elems.size() - 1);
        return result;
    }
};


