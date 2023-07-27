/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tptr.h

Abstract:

    Support for tagged pointers and other low level pointer manipulation macros.

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/

#pragma once

#include <cstdint>
#include "util/machine.h"
#include "util/debug.h"

#define TAG_SHIFT        PTR_ALIGNMENT
#define ALIGNMENT_VALUE  (1 << PTR_ALIGNMENT)
#define TAG_MASK         (ALIGNMENT_VALUE - 1)
#define PTR_MASK         (~TAG_MASK)  

#define ALIGN(T, PTR) reinterpret_cast<T>(((reinterpret_cast<uintptr_t>(PTR) >> PTR_ALIGNMENT) + \
                         static_cast<uintptr_t>((reinterpret_cast<uintptr_t>(PTR) & TAG_MASK) != 0)) << PTR_ALIGNMENT)

#define UNTAG(T, PTR) reinterpret_cast<T>(reinterpret_cast<uintptr_t>(PTR) & PTR_MASK)

#define TAG(T, PTR, TAG_VAL) reinterpret_cast<T>(reinterpret_cast<uintptr_t>(PTR) | static_cast<uintptr_t>(TAG_VAL))

#define GET_TAG(PTR) (reinterpret_cast<uintptr_t>(PTR) & TAG_MASK)

#define BOXINT(T, VAL) reinterpret_cast<T>(static_cast<uintptr_t>(VAL) << PTR_ALIGNMENT)

#define BOXTAGINT(T, VAL, TAG_VAL) reinterpret_cast<T>((static_cast<uintptr_t>(VAL) << PTR_ALIGNMENT) | static_cast<uintptr_t>(TAG_VAL))

#define UNBOXINT(PTR) static_cast<int>(reinterpret_cast<uintptr_t>(PTR) >> PTR_ALIGNMENT)

template <typename U, typename T>
U unbox(T* ptr) {
    return static_cast<U>(reinterpret_cast<std::uintptr_t>(ptr) >> PTR_ALIGNMENT);
}

template <typename T>
unsigned get_tag(T* ptr) {
    return reinterpret_cast<std::uintptr_t>(ptr) & TAG_MASK;
}

template <typename T, typename U>
T* box(U val, std::uintptr_t tag = 0) {
    static_assert( sizeof(T*) >= sizeof(U) + PTR_ALIGNMENT );
    SASSERT_EQ(tag & PTR_MASK, 0);
    T* ptr = reinterpret_cast<T*>((static_cast<std::uintptr_t>(val) << PTR_ALIGNMENT) | tag);
    SASSERT_EQ(val, unbox<U>(ptr));  // roundtrip of conversion integer -> pointer -> integer is not actually guaranteed by the C++ standard (but seems fine in practice, as indicated by previous usage of BOXINT/UNBOXINT)
    SASSERT_EQ(tag, get_tag(ptr));
    return ptr;
}
