/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
#include "util/lp/binary_heap_priority_queue.h"
namespace lp {

class indexer_of_constraints {
    binary_heap_priority_queue<unsigned> m_queue_of_released_indices;
    unsigned m_max;
public:
    indexer_of_constraints() :m_max(0) {}
    unsigned get_new_index() {
        unsigned ret;
        if (m_queue_of_released_indices.is_empty()) {
            ret = m_max++;
        }
        else {
            ret = m_queue_of_released_indices.dequeue();
        }
        return ret;
    };
    void release_index(unsigned i) {
        m_queue_of_released_indices.enqueue(i, i);
    };
    unsigned max() const { return m_max; }
};
}
