/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    buffer.h

Author:

    Daniel Schemmel 2019-2-23

--*/

#ifndef BUFFER_H_
#define BUFFER_H_

#include "old_buffer.h"

template<typename T, bool CallDestructors=true, unsigned INITIAL_SIZE=16>
using buffer = old_buffer<T, CallDestructors, INITIAL_SIZE>;

// note that the append added in the old_ptr_buffer is actually not an addition over its base class old_buffer,
// which already has an append function with the same signature and implementation
template<typename T, unsigned INITIAL_SIZE=16>
using ptr_buffer = old_ptr_buffer<T, INITIAL_SIZE>;

template<typename T, unsigned INITIAL_SIZE=16>
using sbuffer = old_sbuffer<T, INITIAL_SIZE>;

#endif /* BUFFER_H_ */
