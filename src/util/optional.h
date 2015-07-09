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

#ifndef OPTIONAL_H_
#define OPTIONAL_H_

template<typename T>
class optional {
    char m_obj[sizeof(T)];
    char m_initialized;

    void construct(const T & val) {
        m_initialized = 1;
        new (reinterpret_cast<void *>(m_obj)) T(val);
    }

    void destroy() {
        if (m_initialized == 1) {
            reinterpret_cast<T *>(m_obj)->~T();
        }
        m_initialized = 0;
    }

public:
    optional():
        m_initialized(0) {}

    explicit optional(const T & val) {
        construct(val);
    }

    optional(const optional<T> & val):
        m_initialized(0) {
        if (val.m_initialized == 1) {
            construct(*val);
        }
    }

    ~optional() {
        destroy();
    }
    
    static optional const & undef() { static optional u;  return u; }
 
    bool initialized() const { return m_initialized == 1; }
    operator bool() const { return m_initialized == 1; }
    bool operator!() const { return m_initialized == 0; }
    
    T * get() const { 
        if (m_initialized == 1) {
            return reinterpret_cast<T *>(m_obj);
        }
        else {
            return 0;
        }
    }

    void set_invalid() {
        if (m_initialized == 1) {
            destroy();
        }
    }

    T * operator->() {
        SASSERT(m_initialized==1);
        return reinterpret_cast<T *>(m_obj);
    }

    T const * operator->() const {
        SASSERT(m_initialized==1);
        return reinterpret_cast<T const *>(m_obj);
    }

    const T & operator*() const {
        SASSERT(m_initialized==1);
        return *reinterpret_cast<T const*>(m_obj);
    }
    
    T & operator*() {
        SASSERT(m_initialized==1);
        return *reinterpret_cast<T *>(m_obj);
    }

    optional & operator=(const T & val) {
        destroy();
        construct(val);
        return * this;
    }

    optional & operator=(const optional & val) {
        if (&val != this) {
            destroy();
            if (val.m_initialized) {
                construct(*val);
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
    
    optional():m_ptr(0) {}

    explicit optional(T * val):m_ptr(val) {}
    
    optional(const optional & val):m_ptr(val.m_ptr) {}

    static optional const & undef() { return m_undef; }

    bool initialized() const { return m_ptr != 0 ; }

    operator bool() const { return m_ptr != 0; }

    bool operator!() const { return m_ptr == 0; }

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


#endif /* OPTIONAL_H_ */

