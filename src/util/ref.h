/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ref.h

Abstract:

    Simple smart pointer class

Author:

    Leonardo de Moura (leonardo) 2007-08-14.

Revision History:

--*/
#pragma once
#include <utility>

template<typename T>
class ref {
    T * m_ptr;

    void inc_ref() {
        if (m_ptr) {
            m_ptr->inc_ref();
        }
    }

    void dec_ref() {
        if (m_ptr) {
            m_ptr->dec_ref();
        }
    }

public:
    ref():
        m_ptr(nullptr) {
    }

    ref(T * ptr):
        m_ptr(ptr) {
        inc_ref();
    }

    ref(const ref & r):
        m_ptr(r.m_ptr) {
        inc_ref();
    }

   ref (ref && r) noexcept : m_ptr(nullptr) {
       std::swap(m_ptr, r.m_ptr);
   }

    ~ref() {
        dec_ref();
    }

    T * operator->() const {
        return m_ptr;
    }

    T * get() const {
        return m_ptr;
    }

    operator bool() const {
        return m_ptr != nullptr;
    }

    const T & operator*() const {
        return *m_ptr;
    }

    T & operator*() {
        return *m_ptr;
    }

    ref & operator=(T * ptr) {
        if (ptr)
            ptr->inc_ref();
        dec_ref();
        m_ptr = ptr;
        return *this;
    }

    ref & operator=(ref & r) {
        r.inc_ref();
        dec_ref();
        m_ptr = r.m_ptr;
        return *this;
    }

    ref & operator=(ref &&r) {
        if (this != &r) {
           dec_ref ();
           m_ptr = r.detach ();
        }
        return *this;
    }

    void reset() {
        dec_ref();
        m_ptr = nullptr;
    }

    T* detach() { 
        T* tmp = m_ptr;
        m_ptr = nullptr;
        return tmp;
    }

    friend bool operator==(const ref & r1, const ref & r2) {
        return r1.m_ptr == r2.m_ptr;
    }

    friend bool operator!=(const ref & r1, const ref & r2) {
        return r1.m_ptr != r2.m_ptr;
    }
    friend void swap (ref &r1, ref &r2) {
        T* tmp = r1.m_ptr;
        r1.m_ptr = r2.m_ptr;
        r2.m_ptr = tmp;
    }
};

/**
   \brief Manager for references that are not managed.
   This class is used for allowing us to create instantiations of the ref_vector and ref_buffer
   templates for unmanaged objects.
*/
template<typename T>
class unmanged_ref_manager {
    static void inc_ref(T * o) { o->inc_ref(); }
    static void dec_ref(T * o) { o->dec_ref(); }
};


