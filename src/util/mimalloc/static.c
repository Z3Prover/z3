/* ----------------------------------------------------------------------------
Copyright (c) 2018-2020, Microsoft Research, Daan Leijen
This is free software; you can redistribute it and/or modify it under the
terms of the MIT license. A copy of the license can be found in the file
"LICENSE" at the root of this distribution.
-----------------------------------------------------------------------------*/
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif
#if defined(__sun)
// same remarks as os.c for the static's context.
#undef _XOPEN_SOURCE
#undef _POSIX_C_SOURCE
#endif

#include "util/mimalloc/mimalloc.h"
#include "util/mimalloc/mimalloc-internal.h"

// For a static override we create a single object file
// containing the whole library. If it is linked first
// it will override all the standard library allocation
// functions (on Unix's).
#include "util/mimalloc/stats.c"
#include "util/mimalloc/random.c"
#include "util/mimalloc/os.c"
#include "util/mimalloc/bitmap.c"
#include "util/mimalloc/arena.c"
#include "util/mimalloc/segment-cache.c"
#include "util/mimalloc/segment.c"
#include "util/mimalloc/page.c"
#include "util/mimalloc/heap.c"
#include "util/mimalloc/alloc.c"
#include "util/mimalloc/alloc-aligned.c"
#include "util/mimalloc/alloc-posix.c"
#if MI_OSX_ZONE
#include "util/mimalloc/alloc-override-osx.c"
#endif
#include "util/mimalloc/init.c"
#include "util/mimalloc/options.c"
