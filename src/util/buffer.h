
/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    buffer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-10-16.
    Daniel Schemmel 2019-2-23

Revision History:


--*/
#pragma once

#include <type_traits>
#include "util/memory_manager.h"

template<typename T, bool CallDestructors=true, unsigned INITIAL_SIZE=16>
class buffer {
protected:
    T *      m_buffer = reinterpret_cast<T*>(m_initial_buffer);
    unsigned m_pos = 0;
    unsigned m_capacity = INITIAL_SIZE;
    typename std::aligned_storage<sizeof(T), alignof(T)>::type m_initial_buffer[INITIAL_SIZE];

    void free_memory() {
        if (m_buffer != reinterpret_cast<T*>(m_initial_buffer)) {
            dealloc_svect(m_buffer);
        }
    }

    void expand() {
        static_assert(std::is_nothrow_move_constructible<T>::value);
        unsigned new_capacity = m_capacity << 1;
        T * new_buffer        = reinterpret_cast<T*>(memory::allocate(sizeof(T) * new_capacity));
        for (unsigned i = 0; i < m_pos; ++i) {
            new (&new_buffer[i]) T(std::move(m_buffer[i]));
            if (CallDestructors) {
                m_buffer[i].~T();
            }
        }
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
    typedef T data_t;
    typedef T * iterator;
    typedef const T * const_iterator;

    buffer() = default;
    
    buffer(const buffer & source) {
        for (unsigned i = 0, sz = source.size(); i < sz; ++i) {
            push_back(source.m_buffer[i]);
        }
    }

    buffer(buffer && source) noexcept {
        if (source.m_buffer == reinterpret_cast<T*>(source.m_initial_buffer)) {
            for (unsigned i = 0, sz = source.size(); i < sz; ++i) {
                push_back(std::move(source.m_buffer[i]));
            }
        } else {
            m_buffer          = source.m_buffer;
            m_pos             = source.m_pos;
            m_capacity        = source.m_capacity;
            source.m_buffer   = reinterpret_cast<T*>(source.m_initial_buffer);
            source.m_pos      = 0;
            source.m_capacity = INITIAL_SIZE;
        }
    }

    buffer(unsigned sz, const T & elem) {
        for (unsigned i = 0; i < sz; i++) {
            push_back(elem);
        }
        SASSERT(size() == sz);
    }
    
    ~buffer() {
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
    
    T * data() const {
        return m_buffer;
    }

    void append(unsigned n, T const * elems) {
        for (unsigned i = 0; i < n; i++) {
            push_back(elems[i]);
        }
    }

    void append(const buffer& source) {
        append(source.size(), source.data());
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

    buffer & operator=(buffer const & other) {
        if (this == &other)
            return *this;
        reset();
        append(other);
        return *this;
    }
};

// note that the append added is actually not an addition over its base class buffer,
// which already has an append function with the same signature and implementation

template<typename T, unsigned INITIAL_SIZE=16>
class ptr_buffer : public buffer<T *, false, INITIAL_SIZE> {
public:
    void append(unsigned n, T * const * elems) {
        for (unsigned i = 0; i < n; i++) {
            this->push_back(elems[i]);
        }
    }
};

template<typename T, unsigned INITIAL_SIZE=16>
class sbuffer : public buffer<T, false, INITIAL_SIZE> {
public:
    sbuffer(): buffer<T, false, INITIAL_SIZE>() {}
    sbuffer(unsigned sz, const T& elem) : buffer<T, false, INITIAL_SIZE>(sz,elem) {}
};
