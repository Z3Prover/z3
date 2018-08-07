
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
#include "util/vector.h"
#include "util/debug.h"
#include "util/lp/lp_utils.h"
namespace lp {
// the elements with the smallest priority are dequeued first
template <typename T>
class binary_heap_priority_queue {
    vector<T> m_priorities;

    // indexing for A starts from 1
    vector<unsigned> m_heap; // keeps the elements of the queue
    vector<int> m_heap_inverse; // o = m_heap[m_heap_inverse[o]]
    unsigned m_heap_size;
    // is is the child place in heap
    void swap_with_parent(unsigned i);
    void put_at(unsigned i, unsigned h);
    void decrease_priority(unsigned o, T newPriority);
public:
#ifdef Z3DEBUG
    bool is_consistent() const;
#endif
public:
    void remove(unsigned o);
    unsigned size() const { return m_heap_size; }
    binary_heap_priority_queue(): m_heap(1), m_heap_size(0) {} // the empty constructror
    // n is the initial queue capacity.
    // The capacity will be enlarged each time twice if needed
    binary_heap_priority_queue(unsigned n);

    void clear() {
        for (unsigned i = 0; i < m_heap_size; i++) {
            unsigned o = m_heap[i+1];
            m_heap_inverse[o] = -1;
        }
        m_heap_size = 0;
    }

    void resize(unsigned n);
    void put_to_heap(unsigned i, unsigned o);

    void enqueue_new(unsigned o, const T& priority);

    // This method can work with an element that is already in the queue.
    // In this case the priority will be changed and the queue adjusted.
    void enqueue(unsigned o, const T & priority);
    void change_priority_for_existing(unsigned o, const T & priority);
    T get_priority(unsigned o) const { return m_priorities[o]; }
    bool is_empty() const { return m_heap_size == 0; }

    /// return the first element of the queue and removes it from the queue
    unsigned dequeue_and_get_priority(T & priority);
    void fix_heap_under(unsigned i);
    void put_the_last_at_the_top_and_fix_the_heap();
    /// return the first element of the queue and removes it from the queue
    unsigned dequeue();
    unsigned peek() const {
        lp_assert(m_heap_size > 0);
        return m_heap[1];
    }
    void print(std::ostream & out);
};
}
