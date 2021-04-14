/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ref_buffer.h

Abstract:

    Buffer of smart pointers.

Author:

    Leonardo de Moura (leonardo) 2008-01-04.

Revision History:

--*/
#pragma once

#include "util/buffer.h"
#include "util/obj_ref.h"
#include "util/ref_vector.h"


/**
   \brief Buffer of smart pointers.
   Ref must provide the methods
   - void dec_ref(T * obj)
   - void inc_ref(T * obj)
*/
template<typename T, typename Ref, unsigned INITIAL_SIZE=16>
class ref_buffer_core : public Ref {
protected:
    ptr_buffer<T, INITIAL_SIZE> m_buffer;

    void inc_ref(T * o) { Ref::inc_ref(o); }
    void dec_ref(T * o) { Ref::dec_ref(o); }

    void dec_range_ref(T * const * begin, T * const * end) {
        for (T * const * it = begin; it < end; ++it)
            dec_ref(*it);
    }

public:
    typedef T * data_t;

    ref_buffer_core(Ref const & r = Ref()):
        Ref(r) {
    }

    ~ref_buffer_core() {
        dec_range_ref(m_buffer.begin(), m_buffer.end());
    }

    void push_back(T * n) {
        inc_ref(n);
        m_buffer.push_back(n);
    }

    template <typename M>
    void push_back(obj_ref<T,M> && n) {
        m_buffer.push_back(n.get());
        n.steal();
    }
    
    void pop_back() {
        SASSERT(!m_buffer.empty());
        T * n = m_buffer.back();
        m_buffer.pop_back();
        dec_ref(n);
    }
    
    T * back() const { 
        return m_buffer.back();
    }

    T * & back() { 
        return m_buffer.back();
    }
    
    T ** data() const {
        return m_buffer.data();
    }

    T * operator[](unsigned idx) const {
        return m_buffer[idx];
    }

    T* const* begin() const { return data(); }
    T* const* end() const { return data() + size(); }

    void set(unsigned idx, T * n) {
        inc_ref(n);
        dec_ref(m_buffer[idx]);
        m_buffer[idx] = n;
    }

    unsigned size() const {
        return m_buffer.size();
    }

    bool empty() const {
        return m_buffer.empty();
    }

    void reset() {
        dec_range_ref(m_buffer.begin(), m_buffer.end());
        m_buffer.reset();
    }

    void finalize() {
        dec_range_ref(m_buffer.begin(), m_buffer.end());
        m_buffer.finalize();
    }        

    void append(unsigned n, T * const * elems) {
        for (unsigned i = 0; i < n; i++) {
            push_back(elems[i]);
        }
    }

    void append(ref_buffer_core const & other) {
        append(other.size(), other.data());
    }

    void resize(unsigned sz) {
        if (sz < m_buffer.size())
            dec_range_ref(m_buffer.begin() + sz, m_buffer.end());
        m_buffer.resize(sz, 0);
    }

    void shrink(unsigned sz) {
        SASSERT(sz <= m_buffer.size());
        resize(sz);
    }

    // set pos idx with elem. If idx >= size, then expand. 
    void setx(unsigned idx, T * elem) {
        if (idx >= size()) {
            resize(idx+1);
        }
        set(idx, elem);
    }

    ref_buffer_core & operator=(ref_buffer_core const & other) {
        if (this == &other)
            return *this;
        reset();
        append(other);
        return *this;
    }
};


/**
   \brief Buffer of managed references
*/
template<typename T, typename TManager, unsigned INITIAL_SIZE=16>
class ref_buffer : public ref_buffer_core<T, ref_manager_wrapper<T, TManager>, INITIAL_SIZE> {
    typedef ref_buffer_core<T, ref_manager_wrapper<T, TManager>, INITIAL_SIZE> super;
public:
    ref_buffer(TManager & m):
        super(ref_manager_wrapper<T, TManager>(m)) {
    }

    ref_buffer(ref_buffer const & other):
        super(ref_manager_wrapper<T, TManager>(other.m_manager)) {
        SASSERT(this->m_buffer.size() == 0);
        append(other);
    }        
};

/**
   \brief Buffer of unmanaged references
*/
template<typename T, unsigned INITIAL_SIZE=16>
class sref_buffer : public ref_buffer_core<T, ref_unmanaged_wrapper<T>, INITIAL_SIZE> {
public:
};

