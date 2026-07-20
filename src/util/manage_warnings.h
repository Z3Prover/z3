/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    build_warnings.h

Abstract:

    Macros to control compiler build warnings.

Author:

    Dave Detlefs 2026-07-20.

Revision History:

--*/
#pragma once

// #define PRAGMA_MACRO(s) _Pragma(s)

// In some cases, we wish to be able to terminate macros with semicolons,
// even when the semi is (strictly speaking) illegal when following the
// expansion of the macro.  (The macro invocations can look like function
// invocations to some IDE's, and the lack of a trailing semi can confuse them.)
// In those cases, we add this DUMMY_DECL to the macro; it "consumes" the trailing
// semi, making it legal.

// Standard preprocessor concatenation gymnastics
#define CONCAT_IMPL(x, y) x##y
#define CONCAT(x, y) CONCAT_IMPL(x, y)

#define DUMMY_DECL using CONCAT(__dummy_decl_, __COUNTER__) = int

#define DO_PRAGMA(x) _Pragma(#x)

#ifdef __clang__

#define START_DISABLE_WARNING(s)		\
  _Pragma("clang diagnostic push")		\
  DO_PRAGMA(clang diagnostic ignored #s)


#define END_DISABLE_WARNING			\
  _Pragma("clang diagnostic pop")		\
  DUMMY_DECL

#define START_DISABLE_EXTRA_SEMI_WARNING START_DISABLE_WARNING(-Wextra-semi)

#else

#define START_DISABLE_EXTRA_SEMI_WARNING
#define END_DISABLE_WARNING

#endif




