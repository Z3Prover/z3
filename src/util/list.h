/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    list.h

Abstract:

    Simple list data structure. It is meant to be used with region allocators.

Author:

    Leonardo de Moura (leonardo) 2007-07-10.

Revision History:

--*/
#pragma once

#include "util/buffer.h"
#include "util/region.h"

template<typename T>
class list {
    T      m_head;
    list * m_tail;

public:
    list(T const & h, list * t = nullptr):
        m_head(h),
        m_tail(t) {
    }

    T const & head() const { return m_head; }
    list * tail() const { return m_tail; }
    T & head() { return m_head; }
    list * & tail() { return m_tail; }

    class iterator {
        list const * m_curr;
    public:
        iterator(list const * c = 0):m_curr(c) {}
        T const & operator*() const { return m_curr->head(); }
        iterator & operator++() { m_curr = m_curr->tail(); return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const & it) { return m_curr == it.m_curr; }
        bool operator!=(iterator const & it) { return m_curr != it.m_curr; }
    };        

    typedef iterator const_iterator;
    iterator begin() const { return iterator(this); }
    iterator end() const { return iterator(0); }
};

/**
   \brief Return the list length.
*/
template<typename T>
unsigned length(list<T> * l) {
    unsigned r = 0;
    while(l) {
        l = l->tail();
        r++;
    }
    return r;
}

/**
   \brief Non destructive append operation.  The new nodes are allocated
   using the given region allocator.
*/
template<typename T>
list<T> * append(region & r, list<T> * l1, list<T> * l2) {
    if (l2 == nullptr) {
        return l1;
    }
    ptr_buffer<list<T> > buffer;
    while (l1) {
        buffer.push_back(l1);
        l1 = l1->tail();
    }
    list<T> * result = l2;
    typename ptr_buffer<list<T> >::const_iterator it    = buffer.end();
    typename ptr_buffer<list<T> >::const_iterator begin = buffer.begin();
    while (it != begin) {
        --it;
        list<T> * curr = *it;
        result = new (r) list<T>(curr->head(), result);
    }
    return result;
}


