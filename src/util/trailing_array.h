#pragma once

// Copyright (c) Microsoft Corporation. All Rights Reserved.

// Many classes in Z3 use the "trailing array" idiom: the last field
// of the class C is a zero-length array of some type T, and the allocation
// of an instance adds extra space for some number of T's (usually the
// number is held in some other field of C).

// Zero-length arrays are non-standard, and provoke a warning in Clang
// when -Wzero-length-array is specified.  This file introduces a macro
// for this idiom, which, for compilers that give a warning, disables
// the warning around the declaration.  So far that's only Clang,
// but more could be added.

#define STR_PRAGMA_FOR_TRAILING_ARRAY(x) _Pragma(#x)

#ifdef __clang__
#define TRAILING_ARRAY(type, field)					\
  STR_PRAGMA_FOR_TRAILING_ARRAY(clang diagnostic push)			\
  STR_PRAGMA_FOR_TRAILING_ARRAY(clang diagnostic ignored "-Wzero-length-array") \
  type field[0];							\
  STR_PRAGMA_FOR_TRAILING_ARRAY(clang diagnostic pop)

#else
#define TRAILING_ARRAY(type, field) type field[0];

#endif

