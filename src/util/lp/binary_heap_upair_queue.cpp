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
#include "util/lp/binary_heap_upair_queue_def.h"
namespace lp {
template binary_heap_upair_queue<int>::binary_heap_upair_queue(unsigned int);
template binary_heap_upair_queue<unsigned int>::binary_heap_upair_queue(unsigned int);
template unsigned binary_heap_upair_queue<int>::dequeue_available_spot();
template unsigned binary_heap_upair_queue<unsigned int>::dequeue_available_spot();
template void binary_heap_upair_queue<int>::enqueue(unsigned int, unsigned int, int const&);
template void binary_heap_upair_queue<int>::remove(unsigned int, unsigned int);
template void binary_heap_upair_queue<unsigned int>::remove(unsigned int, unsigned int);
template void binary_heap_upair_queue<int>::dequeue(unsigned int&, unsigned int&);
template void binary_heap_upair_queue<unsigned int>::enqueue(unsigned int, unsigned int, unsigned int const&);
template void binary_heap_upair_queue<unsigned int>::dequeue(unsigned int&, unsigned int&);
}
