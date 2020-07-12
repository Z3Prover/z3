/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    optional.h

Abstract:

    Discriminated union of a type T.
    It defines the notion of initialized/uninitialized objects.

Author:

    Leonardo de Moura (leonardo) 2006-09-29.

Revision History:

--*/

#pragma once

template<class T>
class optional {
    T* m_obj = nullptr;

    void destroy() {
        dealloc(m_obj);
        m_obj = nullptr;
    }

public:
    optional() {}

    explicit optional(const T & val) {
        m_obj = alloc(T, val);
    }

    explicit optional(T && val) {
        m_obj = alloc(T, std::move(val));
    }

    optional(optional<T> && val) noexcept {
        std::swap(m_obj, val.m_obj);
    }

    optional(const optional<T> & val) {
        if (val.m_obj) {
            m_obj = alloc(T, *val);
        }
    }

    ~optional() {
        destroy();
    }
    
    static optional const & undef() { static optional u;  return u; }
 
    bool initialized() const { return m_obj; }
    operator bool() const { return m_obj; }
    bool operator!() const { return !m_obj; }
    
    T * get() const { 
        return m_obj;
    }

    void set_invalid() {
        destroy();
    }

    T * operator->() {
        SASSERT(m_obj);
        return m_obj;
    }

    T const * operator->() const {
        SASSERT(m_obj);
        return m_obj;
    }

    const T & operator*() const {
        SASSERT(m_obj);
        return *m_obj;
    }
    
    T & operator*() {
        SASSERT(m_obj);
        return *m_obj;
    }

    optional & operator=(const T & val) {
        destroy();
        m_obj = alloc(T, val);
        return * this;
    }

    optional & operator=(optional && val) {
        std::swap(m_obj, val.m_obj);
        return *this;
    }

    optional & operator=(const optional & val) {
        if (&val != this) {
            destroy();
            if (val.m_obj) {
                m_obj = alloc(T, *val);
            }
        }
        return *this;
    }
};


/**
   \brief Template specialization for pointers. NULL represents uninitialized pointers.
 */
template<typename T>
class optional<T*> {
    T * m_ptr;

    static optional m_undef;

public:
    
    optional():m_ptr(nullptr) {}

    explicit optional(T * val):m_ptr(val) {}

    static optional const & undef() { return m_undef; }

    bool initialized() const { return m_ptr != 0 ; }

    operator bool() const { return m_ptr != 0; }

    bool operator!() const { return m_ptr == nullptr; }

    void reset() { m_ptr = 0; }

    optional & operator=(T * val) {
        m_ptr = val;
        return *this;
    }

    optional & operator=(const optional & val) {
        m_ptr = val.m_ptr;
        return *this;
    }

    T ** operator->() { return &m_ptr; }

    T * operator*() const { return m_ptr; }
    
    T * & operator*() { return m_ptr; }
};
