/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    uint_map.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-07-01.

Revision History:

--*/
#ifndef UINT_MAP_H_
#define UINT_MAP_H_

#include "util/vector.h"

/**
   \brief Implement a map from unsigned to T * using vectors
*/
template<typename T>
class uint_map {
    ptr_vector<T> m_map;
public:
    bool contains(unsigned k) const { return m_map.get(k, 0) != 0; }

    bool find(unsigned k, T * & v) const { 
        if (k >= m_map.size())
            return false;
        else {
            v = m_map[k];
            return v != 0;
        }
    }
    
    T * find(unsigned k) const { 
        SASSERT(k < m_map.size() && m_map[k] != 0); 
        return m_map[k]; 
    }

    void insert(unsigned k, T * v) {
        m_map.reserve(k+1);
        m_map[k] = v;
        SASSERT(contains(k));
    }

    void erase(unsigned k) {
        if (k < m_map.size()) 
            m_map[k] = 0;
    }

    void reset() {
        m_map.reset();
    }
};


#endif /* UINT_MAP_H_ */

