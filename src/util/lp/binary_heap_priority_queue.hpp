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
#include "util/vector.h"
#include "util/lp/binary_heap_priority_queue.h"
namespace lp {
// this is the child place in the heap
template <typename T> void binary_heap_priority_queue<T>::swap_with_parent(unsigned i) {
    unsigned parent = m_heap[i >> 1];
    put_at(i >> 1, m_heap[i]);
    put_at(i, parent);
}

template <typename T> void binary_heap_priority_queue<T>::put_at(unsigned i, unsigned h) {
    m_heap[i] = h;
    m_heap_inverse[h] = i;
}

template <typename T> void binary_heap_priority_queue<T>::decrease_priority(unsigned o, T newPriority) {
    m_priorities[o] = newPriority;
    int i = m_heap_inverse[o];
    while (i > 1) {
        if (m_priorities[m_heap[i]] < m_priorities[m_heap[i >> 1]])
            swap_with_parent(i);
        else
            break;
        i >>= 1;
    }
}

#ifdef Z3DEBUG
template <typename T> bool binary_heap_priority_queue<T>::is_consistent() const {
    for (int i = 0; i < m_heap_inverse.size(); i++) {
        int i_index = m_heap_inverse[i];
        SASSERT(i_index <= static_cast<int>(m_heap_size));
        SASSERT(i_index == -1 || m_heap[i_index] == i);
    }
    for (unsigned i = 1; i < m_heap_size; i++) {
        unsigned ch = i << 1;
        for (int k = 0; k < 2; k++) {
            if (ch > m_heap_size) break;
            if (!(m_priorities[m_heap[i]] <= m_priorities[m_heap[ch]])){
                return false;
            }
            ch++;
        }
    }
    return true;
}
#endif

template <typename T> void binary_heap_priority_queue<T>::remove(unsigned o) {
    T priority_of_o = m_priorities[o];
    int o_in_heap = m_heap_inverse[o];
    if (o_in_heap == -1)  {
        return;  // nothing to do
    }
    SASSERT(static_cast<unsigned>(o_in_heap) <= m_heap_size);
    if (static_cast<unsigned>(o_in_heap) < m_heap_size) {
        put_at(o_in_heap, m_heap[m_heap_size--]);
        if (m_priorities[m_heap[o_in_heap]] > priority_of_o) {
            fix_heap_under(o_in_heap);
        } else { // we need to propogate the m_heap[o_in_heap] up
            unsigned i = o_in_heap;
            while (i > 1) {
                unsigned ip = i >> 1;
                if (m_priorities[m_heap[i]] < m_priorities[m_heap[ip]])
                    swap_with_parent(i);
                else
                    break;
                i = ip;
            }
        }
    } else {
        SASSERT(static_cast<unsigned>(o_in_heap) == m_heap_size);
        m_heap_size--;
    }
    m_heap_inverse[o] = -1;
    // SASSERT(is_consistent());
}
// n is the initial queue capacity.
// The capacity will be enlarged two times automatically if needed
template <typename T> binary_heap_priority_queue<T>::binary_heap_priority_queue(unsigned n) :
    m_priorities(n),
    m_heap(n + 1), // because the indexing for A starts from 1
    m_heap_inverse(n, -1),
    m_heap_size(0)
{ }


template <typename T> void binary_heap_priority_queue<T>::resize(unsigned n) {
    m_priorities.resize(n);
    m_heap.resize(n + 1);
    m_heap_inverse.resize(n, -1);
}

template <typename T> void binary_heap_priority_queue<T>::put_to_heap(unsigned i, unsigned o) {
    m_heap[i] = o;
    m_heap_inverse[o] = i;
}

template <typename T> void binary_heap_priority_queue<T>::enqueue_new(unsigned o, const T& priority) {
    m_heap_size++;
    int i = m_heap_size;
    SASSERT(o < m_priorities.size());
    m_priorities[o] = priority;
    put_at(i, o);
    while (i > 1 && m_priorities[m_heap[i >> 1]] > priority) {
        swap_with_parent(i);
        i >>= 1;
    }
}
// This method can work with an element that is already in the queue.
// In this case the priority will be changed and the queue adjusted.
template <typename T> void binary_heap_priority_queue<T>::enqueue(unsigned o, const T & priority) {
    if (o >= m_priorities.size()) {
        resize(o << 1); // make the size twice larger
    }
    if (m_heap_inverse[o] == -1)
        enqueue_new(o, priority);
    else
        change_priority_for_existing(o, priority);
}

template <typename T> void binary_heap_priority_queue<T>::change_priority_for_existing(unsigned o, const T & priority) {
    if (m_priorities[o] > priority) {
        decrease_priority(o, priority);
    } else {
        m_priorities[o] = priority;
        fix_heap_under(m_heap_inverse[o]);
    }
}


/// return the first element of the queue and removes it from the queue
template <typename T> unsigned binary_heap_priority_queue<T>::dequeue_and_get_priority(T & priority) {
    SASSERT(m_heap_size != 0);
    int ret = m_heap[1];
    priority = m_priorities[ret];
    put_the_last_at_the_top_and_fix_the_heap();
    return ret;
}

template <typename T> void binary_heap_priority_queue<T>::fix_heap_under(unsigned i) {
    while (true) {
        unsigned smallest = i;
        unsigned l = i << 1;
        if (l <= m_heap_size && m_priorities[m_heap[l]] < m_priorities[m_heap[i]])
            smallest = l;
        unsigned r = l + 1;
        if (r <= m_heap_size && m_priorities[m_heap[r]] < m_priorities[m_heap[smallest]])
            smallest = r;
        if (smallest != i)
            swap_with_parent(smallest);
        else
            break;
        i = smallest;
    }
}

template <typename T> void binary_heap_priority_queue<T>::put_the_last_at_the_top_and_fix_the_heap() {
    if (m_heap_size > 1) {
        put_at(1, m_heap[m_heap_size--]);
        fix_heap_under(1);
    } else {
        m_heap_size--;
    }
}
/// return the first element of the queue and removes it from the queue
template <typename T> unsigned binary_heap_priority_queue<T>::dequeue() {
    SASSERT(m_heap_size > 0);
    int ret = m_heap[1];
    put_the_last_at_the_top_and_fix_the_heap();
    m_heap_inverse[ret] = -1;
    return ret;
}
#ifdef Z3DEBUG
template <typename T> void binary_heap_priority_queue<T>::print(std::ostream & out) {
    vector<int> index;
    vector<T> prs;
    while (size()) {
        T prior;
        int j = dequeue_and_get_priority(prior);
        index.push_back(j);
        prs.push_back(prior);
        out << "(" << j << ", " << prior << ")";
    }
    out << std::endl;
    // restore the queue
    for (int i = 0; i < index.size(); i++)
        enqueue(index[i], prs[i]);
}
#endif
}
