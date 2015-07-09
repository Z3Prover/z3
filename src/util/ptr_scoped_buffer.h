/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ptr_scoped_buffer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-03-03.

Revision History:

--*/
#ifndef PTR_SCOPED_BUFFER_H_
#define PTR_SCOPED_BUFFER_H_

#include"util.h"
#include"debug.h"
#include"buffer.h"

template<typename T, unsigned INITIAL_SIZE=16, typename D = delete_proc<T> >
class ptr_scoped_buffer : private ptr_buffer<T, INITIAL_SIZE> {
    D m_deallocator;
    void deallocate_all() { 
        typename ptr_buffer<T, INITIAL_SIZE>::iterator it  = ptr_buffer<T, INITIAL_SIZE>::begin();
        typename ptr_buffer<T, INITIAL_SIZE>::iterator end = ptr_buffer<T, INITIAL_SIZE>::end();
        for (; it != end; ++it)
            m_deallocator(*it);
    }
public:
    typedef typename ptr_buffer<T, INITIAL_SIZE>::const_iterator const_iterator;
    ptr_scoped_buffer(D const & m = D()):ptr_buffer<T, INITIAL_SIZE>(), m_deallocator(m) {}
    ~ptr_scoped_buffer() { deallocate_all(); }
    void reset() { deallocate_all(); ptr_buffer<T, INITIAL_SIZE>::reset(); }
    void finalize() { deallocate_all(); ptr_buffer<T, INITIAL_SIZE>::finalize(); }
    /** \brief Release ownership of the pointers stored in the buffer */
    void release() { ptr_buffer<T, INITIAL_SIZE>::reset(); }
    unsigned size() const { return ptr_buffer<T, INITIAL_SIZE>::size(); }
    bool empty() const { return ptr_buffer<T, INITIAL_SIZE>::empty(); }
    const_iterator begin() const { return ptr_buffer<T, INITIAL_SIZE>::begin(); }
    const_iterator end() const { return ptr_buffer<T, INITIAL_SIZE>::end(); }
    void push_back(T * elem) { return ptr_buffer<T, INITIAL_SIZE>::push_back(elem); }
    T * back() const { return ptr_buffer<T, INITIAL_SIZE>::back(); }
    void pop_back() { m_deallocator(back()); ptr_buffer<T, INITIAL_SIZE>::pop_back(); }
    T * get(unsigned idx) const { return ptr_buffer<T, INITIAL_SIZE>::get(idx); }
    void set(unsigned idx, T * e) { T * old_e = get(idx); if (e != old_e) m_deallocator(old_e); ptr_buffer<T, INITIAL_SIZE>::set(idx, e); }
    void append(unsigned n, T * const * elems) { ptr_buffer<T, INITIAL_SIZE>::append(n, elems); }
};

#endif

