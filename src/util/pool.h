/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pool.h

Abstract:

    Object pool.

Author:

    Leonardo de Moura (leonardo) 2007-02-15.

Revision History:

--*/
#ifndef POOL_H_
#define POOL_H_

#include"util.h"
#include"vector.h"

template<typename T>
class pool {
    ptr_vector<T> m_objs;
public:
    ~pool() {
        std::for_each(m_objs.begin(), m_objs.end(), delete_proc<T>());
    }

    T * mk() {
        if (m_objs.empty()) {
            return alloc(T);
        }
        else {
            T * r = m_objs.back();
            m_objs.pop_back();
            return r;
        }
    }
    
    void recycle(T * obj) {
        m_objs.push_back(obj);
    }
};

#endif /* POOL_H_ */

