/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    lockless_queue.h

Abstract:

    A queue that doesn't require locking, as long as only 
    one thread pushes and another thread pops.

Author:

    Christoph Wintersteiger (t-cwinte) 2008-12-26

Revision History:

--*/

#ifndef _LOCKLESS_QUEUE_H_
#define _LOCKLESS_QUEUE_H_

#include <new> 
#include "debug.h"

template<typename T>
class lockless_queue {
protected:
    unsigned m_head;
    unsigned m_tail;
    unsigned m_size;
    T *m_items;
public:
    typedef T value_type;

    lockless_queue(unsigned size=4096) : 
        m_head(0), 
        m_tail(0), 
        m_size(size),
        m_items(0) { 
        if(m_size>0) {
            m_items = alloc_vect<T>(m_size);
            SASSERT(m_items!=0);
        }
    }

    lockless_queue(const lockless_queue &other) {
        m_items = 0;
        m_size = m_head = m_tail = 0;
        this->operator=(other);
    }

    ~lockless_queue() { 
        if(m_items) {
            dealloc_vect(m_items, m_size);
            m_items=0;
        }
    }

    inline bool push(const T& elem) {
        volatile unsigned head = m_head;

        if(((head+1)%m_size) == m_tail)
            return false; // queue is full.

        m_items[head++] = elem;
        head %= m_size;
        m_head = head;
        return true;
    }

    inline bool pop() {
        volatile unsigned tail = m_tail;

        if(tail == m_head)
            return false; // queue is empty.

        tail = (tail+1) % m_size;
        m_tail = tail;
        return true;
    }

    inline T& back() const {
        SASSERT(!empty());
        return m_items[m_tail]; 
    }

    inline bool empty() const {
        return (m_tail == m_head);
    }

	inline bool full() const {
        return (m_tail == ((m_head+1)%m_size));
    }

    lockless_queue& operator=(const lockless_queue &other) {
        if(m_size!=other.m_size) {
            if(m_items) dealloc_vect(m_items, m_size);
            m_items = alloc_vect<T>(other.m_size);
            m_size = other.m_size;
        }

        for(size_t cur = other.m_tail; cur!=other.m_head; cur = (cur+1)%m_size)
            m_items[cur] = other.m_items[cur];

        m_tail = other.m_tail;
        m_head = other.m_head;

        return *this;
    }

};

#endif
