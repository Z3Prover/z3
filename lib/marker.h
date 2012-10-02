/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    marker.h

Abstract:

    Auxiliary object for managing markings

Author:

    Leonardo de Moura (leonardo) 2008-02-07.

Revision History:

--*/
#ifndef _MARKER_H_
#define _MARKER_H_

#include"vector.h"

/**
   \brief Keep track of all marked objects. Unmark them when the method
   unmark or destructor is invoked.
*/
template<typename T>
class marker {
    ptr_vector<T> m_to_unmark;
public:
    ~marker() {
        unmark();
    }

    void mark(T * obj) { 
        obj->set_mark(true);
        m_to_unmark.push_back(obj);
    }
    
    bool is_marked(T * obj) const {
        return obj->is_marked();
    }

    void unmark() {
        typename ptr_vector<T>::iterator it  = m_to_unmark.begin();
        typename ptr_vector<T>::iterator end = m_to_unmark.end();
        for (; it != end; ++it) {
            T * obj = *it;
            obj->set_mark(false);
        }
        m_to_unmark.reset();
    }
};

#endif /* _MARKER_H_ */
