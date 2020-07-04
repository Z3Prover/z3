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

#include "util/machine.h"

#define TAG_SHIFT        PTR_ALIGNMENT
#define ALIGNMENT_VALUE  (1 << PTR_ALIGNMENT)
#define TAG_MASK         (ALIGNMENT_VALUE - 1)
#define PTR_MASK         (~TAG_MASK)  

#define ALIGN(T, PTR) reinterpret_cast<T>(((reinterpret_cast<size_t>(PTR) >> PTR_ALIGNMENT) + \
                         static_cast<size_t>((reinterpret_cast<size_t>(PTR) & TAG_MASK) != 0)) << PTR_ALIGNMENT)

#define UNTAG(T, PTR) reinterpret_cast<T>(reinterpret_cast<size_t>(PTR) & PTR_MASK)

#define TAG(T, PTR, TAG_VAL) reinterpret_cast<T>(reinterpret_cast<size_t>(PTR) | static_cast<size_t>(TAG_VAL))

#define GET_TAG(PTR) (reinterpret_cast<size_t>(PTR) & TAG_MASK)

#define BOXINT(T, VAL) reinterpret_cast<T>(static_cast<size_t>(VAL) << PTR_ALIGNMENT)

#define BOXTAGINT(T, VAL, TAG_VAL) reinterpret_cast<T>((static_cast<size_t>(VAL) << PTR_ALIGNMENT) | static_cast<size_t>(TAG_VAL))

#define UNBOXINT(PTR) static_cast<int>(reinterpret_cast<size_t>(PTR) >> PTR_ALIGNMENT)


