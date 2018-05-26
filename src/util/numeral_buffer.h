/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    numeral_buffer.h

Abstract:

    Basic buffer for managing big nums.

Author:

    Leonardo de Moura (leonardo) 2011-06-18.

Revision History:

--*/
#ifndef NUMERAL_BUFFER_H_
#define NUMERAL_BUFFER_H_

#include "util/vector.h"

template<typename Numeral, typename NumeralManager>
class numeral_buffer {
    NumeralManager &  m_manager;
    vector<Numeral>  m_buffer;
public:
    using numeral = Numeral;
    using manager = NumeralManager;
    using value_type = Numeral;

    numeral_buffer(NumeralManager & m):m_manager(m) {}

    ~numeral_buffer() {
        clear();
    }
    
    NumeralManager & m() const { return m_manager; }

    unsigned size() const { return m_buffer.size(); }
    
    bool empty() const { return m_buffer.empty(); }

    void push_back(Numeral const & num) {
        m_buffer.push_back(Numeral());
        m().set(m_buffer.back(), num);
    }
    
    void pop_back() {
        m().del(m_buffer.back());
        m_buffer.pop_back();
    }

    Numeral & back() {
        return m_buffer.back();
    }

    Numeral const & back() const {
        return m_buffer.back();
    }
    
    Numeral const & operator[](unsigned idx) const {
        return m_buffer[idx];
    }

    Numeral & operator[](unsigned idx) {
        return m_buffer[idx];
    }

    void clear() {
        for (auto& element : m_buffer)
            m().del(element);
        m_buffer.clear();
    }

    Numeral * c_ptr() { return m_buffer.c_ptr(); }

    Numeral* data() { return m_buffer.data(); }
    Numeral const* data() const { return m_buffer.data(); }

    void expand(unsigned sz) {
        m_buffer.expand(sz);
    }

    void swap(vector<Numeral> & other) {
        m_buffer.swap(other);
    }

};

#endif
