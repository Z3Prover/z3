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
#ifndef _NUMERAL_BUFFER_H_
#define _NUMERAL_BUFFER_H_

#include"vector.h"

template<typename Numeral, typename NumeralManager>
class numeral_buffer {
    NumeralManager &  m_manager;
    svector<Numeral>  m_buffer;
public:
    typedef Numeral numeral;
    typedef Numeral data;
    typedef NumeralManager manager;

    numeral_buffer(NumeralManager & m):m_manager(m) {}

    ~numeral_buffer() {
        reset();
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

    void reset() {
        typename vector<Numeral>::iterator it  = m_buffer.begin();
        typename vector<Numeral>::iterator end = m_buffer.end();
        for (; it != end; ++it)
            m().del(*it);
        m_buffer.reset();
    }

    Numeral * c_ptr() { return m_buffer.c_ptr(); }

    void reserve(unsigned sz) {
        m_buffer.reserve(sz);
    }

    void swap(svector<Numeral> & other) {
        m_buffer.swap(other);
    }

};

#endif
