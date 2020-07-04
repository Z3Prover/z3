/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    z3native_stubs.h

Abstract:

    DLL/SO/DYLIB export macros.

Author:

    Christoph (cwinter) 2015-12-12

Notes:

--*/

#pragma once

#if defined _WIN32 || defined __CYGWIN__
  #ifdef __GNUC__
    #define DLL_PUBLIC __attribute__ ((dllexport))
  #else
    #define DLL_PUBLIC __declspec(dllexport)
  #endif
#else
  #if __GNUC__ >= 4
    #define DLL_PUBLIC __attribute__ ((visibility ("default")))
  #else
    #define DLL_PUBLIC
  #endif
#endif
    
