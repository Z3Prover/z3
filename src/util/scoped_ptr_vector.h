/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_ptr_vector.h

Abstract:

    Basic template of scoped ptrs.
    TODO: improve

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#pragma once

#include "util/vector.h"
#include "util/util.h"

template<typename T>
class scoped_ptr_vector {
    ptr_vector<T> m_vector;
public:
    scoped_ptr_vector() = default;
    ~scoped_ptr_vector() { reset(); }
    scoped_ptr_vector(scoped_ptr_vector& other) = delete;
    scoped_ptr_vector& operator=(scoped_ptr_vector& other) = delete;

    scoped_ptr_vector(scoped_ptr_vector&& other) noexcept {
        m_vector.swap(other.m_vector);
    }
    scoped_ptr_vector& operator=(scoped_ptr_vector&& other) noexcept {
        if (this == &other)
            return *this;
        reset();
        m_vector.swap(other.m_vector);
        return *this;
    }

    void reset() { std::for_each(m_vector.begin(), m_vector.end(), delete_proc<T>()); m_vector.reset(); }
    void push_back(T * ptr) { m_vector.push_back(ptr); }
    void push_back(scoped_ptr<T>&& ptr) { push_back(ptr.detach()); }
    void pop_back() { SASSERT(!empty()); set(size()-1, nullptr); m_vector.pop_back(); }
    T * back() const { return m_vector.back(); }
    T * operator[](unsigned idx) const { return m_vector[idx]; }
    T * get(unsigned idx, T* d = nullptr) const { return (0 <= idx && idx < m_vector.size()) ? (*this)[idx] : d; }
    void set(unsigned idx, T * ptr) { 
        if (m_vector[idx] == ptr) 
            return; 
        dealloc(m_vector[idx]); 
        m_vector[idx] = ptr; 
    }
    void swap(unsigned i, unsigned j) noexcept { std::swap(m_vector[i], m_vector[j]); }
    unsigned size() const { return m_vector.size(); }
    bool empty() const { return m_vector.empty(); }
    void resize(unsigned sz) { 
        if (sz < m_vector.size()) {
            for (unsigned i = m_vector.size(); i-- > sz; )
                dealloc(m_vector[i]);
            m_vector.shrink(sz); 
        }
        else {
            for (unsigned i = m_vector.size(); i < sz; i++)
                push_back(nullptr);
        }
    }
    void reserve(unsigned sz) {
        if (sz >= m_vector.size())
            resize(sz);
    }

    //!< swap last element with given pointer
    void swap_back(scoped_ptr<T> & ptr) {
        SASSERT(!empty());
        T * tmp = ptr.detach();
        ptr = m_vector.back();
        m_vector[m_vector.size()-1] = tmp;
    }

    T* detach_back() {
        SASSERT(!empty());
        T* tmp = m_vector.back();
        m_vector.back() = nullptr;
        return tmp;
    }

    ptr_vector<T> detach() {
        ptr_vector<T> tmp(std::move(m_vector));
        SASSERT(m_vector.empty());
        return tmp;
    }

    T* const* data() const { return m_vector.data(); }

    using const_iterator = typename ptr_vector<T>::const_iterator;
    const_iterator begin() const { return m_vector.begin(); }
    const_iterator end() const { return m_vector.end(); }
};

