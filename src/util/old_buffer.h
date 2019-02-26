/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    old_buffer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-10-16.

Revision History:

   2019-2-23 Renamed to old_buffer from buffer to provide new implementation

--*/
#ifndef OLD_BUFFER_H_
#define OLD_BUFFER_H_

#include<string.h>
#include "util/memory_manager.h"

template<typename T, bool CallDestructors=true, unsigned INITIAL_SIZE=16>
class old_buffer {
protected:
    T *      m_buffer;
    unsigned m_pos;
    unsigned m_capacity;
    char     m_initial_buffer[INITIAL_SIZE * sizeof(T)];
    
    void free_memory() {
        if (m_buffer != reinterpret_cast<T*>(m_initial_buffer)) {
            dealloc_svect(m_buffer);
        }
    }

    void expand() {
        unsigned new_capacity = m_capacity << 1;
        T * new_buffer        = reinterpret_cast<T*>(memory::allocate(sizeof(T) * new_capacity));
        memcpy(new_buffer, m_buffer, m_pos * sizeof(T));
        free_memory();
        m_buffer              = new_buffer;
        m_capacity            = new_capacity;
    }
    
    void destroy_elements() {
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it) {
            it->~T();
        }
    }

    void destroy() {
        if (CallDestructors) {
            destroy_elements(); 
        }
        free_memory();
    }

public:
    typedef T data;
    typedef T * iterator;
    typedef const T * const_iterator;

    old_buffer():
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
    }
    
    old_buffer(const old_buffer & source):
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
        unsigned sz = source.size();
        for(unsigned i = 0; i < sz; i++) {
            push_back(source.m_buffer[i]);
        }
    }
    
    old_buffer(unsigned sz, const T & elem):
        m_buffer(reinterpret_cast<T *>(m_initial_buffer)),
        m_pos(0),
        m_capacity(INITIAL_SIZE) {
        for (unsigned i = 0; i < sz; i++) {
            push_back(elem);
        }
        SASSERT(size() == sz);
    }
    
    ~old_buffer() {
        destroy();
    }
    
    void reset() { 
        if (CallDestructors) {
            destroy_elements();
        }
        m_pos = 0;
    }
    
    void finalize() {
        destroy();
        m_buffer   = reinterpret_cast<T *>(m_initial_buffer);
        m_pos      = 0;
        m_capacity = INITIAL_SIZE;
    }
    
    unsigned size() const { 
        return m_pos;
    }
    
    bool empty() const {
        return m_pos == 0;
    }
    
    iterator begin() { 
        return m_buffer; 
    }

    iterator end() { 
        return m_buffer + size();
    }

    void set_end(iterator it) {
        m_pos = static_cast<unsigned>(it - m_buffer);
        if (CallDestructors) {
            iterator e  = end();
            for (; it != e; ++it) {
                it->~T();
            }
        }
    }
    
    const_iterator begin() const { 
        return m_buffer; 
    }
    
    const_iterator end() const { 
        return m_buffer + size(); 
    }
    
    void push_back(const T & elem) {
        if (m_pos >= m_capacity)
            expand();
        new (m_buffer + m_pos) T(elem);
        m_pos++;
    }

    void push_back(T && elem) {
        if (m_pos >= m_capacity)
            expand();
        new (m_buffer + m_pos) T(std::move(elem));
        m_pos++;
    }
    
    void pop_back() {
        if (CallDestructors) {
            back().~T(); 
        }
        m_pos--;
    }

    const T & back() const { 
        SASSERT(!empty()); 
        SASSERT(m_pos > 0);
        return m_buffer[m_pos - 1]; 
    }

    T & back() { 
        SASSERT(!empty()); 
        SASSERT(m_pos > 0);
        return m_buffer[m_pos - 1]; 
    }
    
    T * c_ptr() const {
        return m_buffer;
    }

    void append(unsigned n, T const * elems) {
        for (unsigned i = 0; i < n; i++) {
            push_back(elems[i]);
        }
    }

    void append(const old_buffer& source) {
        append(source.size(), source.c_ptr());
    }

    T & operator[](unsigned idx) { 
        SASSERT(idx < size()); 
        return m_buffer[idx]; 
    }

    const T & operator[](unsigned idx) const { 
        SASSERT(idx < size()); 
        return m_buffer[idx];
    }

    T & get(unsigned idx) { 
        SASSERT(idx < size()); 
        return m_buffer[idx]; 
    }

    const T & get(unsigned idx) const { 
        SASSERT(idx < size()); 
        return m_buffer[idx];
    }

    void set(unsigned idx, T const & val) { 
        SASSERT(idx < size()); 
        m_buffer[idx] = val;
    }

    void resize(unsigned nsz, const T & elem=T()) {
        unsigned sz = size();
        if (nsz > sz) {
            for (unsigned i = sz; i < nsz; i++) {
                push_back(elem);
            }
        }
        else if (nsz < sz) {
            for (unsigned i = nsz; i < sz; i++) {
                pop_back();
            }
        }
        SASSERT(size() == nsz);
    }

    void shrink(unsigned nsz) {
        unsigned sz = size();
        SASSERT(nsz <= sz);
        for (unsigned i = nsz; i < sz; i++)
            pop_back();
        SASSERT(size() == nsz);
    }

    old_buffer & operator=(old_buffer const & other) {
        if (this == &other)
            return *this;
        reset();
        append(other);
        return *this;
    }
};

template<typename T, unsigned INITIAL_SIZE=16>
class old_ptr_buffer : public old_buffer<T *, false, INITIAL_SIZE> {
public:
    void append(unsigned n, T * const * elems) {
        for (unsigned i = 0; i < n; i++) {
            this->push_back(elems[i]);
        }
    }
};

template<typename T, unsigned INITIAL_SIZE=16>
class old_sbuffer : public old_buffer<T, false, INITIAL_SIZE> {
public:
    old_sbuffer(): old_buffer<T, false, INITIAL_SIZE>() {}
    old_sbuffer(unsigned sz, const T& elem) : old_buffer<T, false, INITIAL_SIZE>(sz,elem) {}
};

#endif /* OLD_BUFFER_H_ */

