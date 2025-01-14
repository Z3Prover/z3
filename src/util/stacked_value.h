/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
// add to value the stack semantics
#include "util/vector.h"
template <typename T> class stacked_value {
    T m_value;    
    vector<T> m_stack;
public:


    void push() {
        m_stack.push_back(m_value);
    }

    void clear(T const& m) {
        pop(m_stack.size());
        m_value = m;
    }
    
    unsigned stack_size() const {
        return m_stack.size();
    }

    void pop() {
        pop(1);
    }
    void pop(unsigned k) {
        while (k-- > 0) {
            if (m_stack.empty())
                return;
            m_value = m_stack.back();
            m_stack.pop_back();
        }
    }

    stacked_value(): m_value() { }
    stacked_value(const T& m) {
        m_value = m;
    }
    stacked_value(const T&& m) {
        m_value = std::move(m);
    }

    void operator=(T &&arg) {
        m_value = std::move(arg);
    }

    void operator=(const T &arg) {
        m_value = arg;
    }

    operator T&() {
        return m_value;
    }
    
    operator const T&() const {
        return m_value;
    }

    T & operator()() {
        return m_value;
    }

    const T & operator()() const {
        return m_value;
    }


};
