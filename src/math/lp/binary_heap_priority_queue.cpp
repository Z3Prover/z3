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
#include "math/lp/numeric_pair.h"
#include "math/lp/binary_heap_priority_queue_def.h"
namespace lp {
template binary_heap_priority_queue<int>::binary_heap_priority_queue(unsigned int);
template unsigned binary_heap_priority_queue<int>::dequeue();
template void binary_heap_priority_queue<int>::enqueue(unsigned int, int const&);
template void binary_heap_priority_queue<double>::enqueue(unsigned int, double const&);
template void binary_heap_priority_queue<mpq>::enqueue(unsigned int, mpq const&);
template void binary_heap_priority_queue<int>::remove(unsigned int);
template unsigned binary_heap_priority_queue<numeric_pair<mpq> >::dequeue();
template unsigned binary_heap_priority_queue<double>::dequeue();
template unsigned binary_heap_priority_queue<mpq>::dequeue();
template void binary_heap_priority_queue<numeric_pair<mpq> >::enqueue(unsigned int, numeric_pair<mpq> const&);
template void binary_heap_priority_queue<numeric_pair<mpq> >::resize(unsigned int);
template void lp::binary_heap_priority_queue<double>::resize(unsigned int);
template binary_heap_priority_queue<unsigned int>::binary_heap_priority_queue(unsigned int);
template void binary_heap_priority_queue<unsigned>::resize(unsigned int);
template unsigned binary_heap_priority_queue<unsigned int>::dequeue();
template void binary_heap_priority_queue<unsigned int>::enqueue(unsigned int, unsigned int const&);
template void binary_heap_priority_queue<unsigned int>::remove(unsigned int);
template void lp::binary_heap_priority_queue<mpq>::resize(unsigned int);
}
