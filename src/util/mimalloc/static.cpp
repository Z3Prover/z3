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
#include "util/mimalloc/stats.ch"
#include "util/mimalloc/random.ch"
#include "util/mimalloc/os.ch"
#include "util/mimalloc/bitmap.ch"
#include "util/mimalloc/arena.ch"
#include "util/mimalloc/segment-cache.ch"
#include "util/mimalloc/segment.ch"
#include "util/mimalloc/page.ch"
#include "util/mimalloc/heap.ch"
#include "util/mimalloc/alloc.ch"
#include "util/mimalloc/alloc-aligned.ch"
#include "util/mimalloc/alloc-posix.ch"
#if MI_OSX_ZONE
#include "util/mimalloc/alloc-override-osx.ch"
#endif
#include "util/mimalloc/init.ch"
#include "util/mimalloc/options.ch"
