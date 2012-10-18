/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_internal.h

Abstract:

    Z3 internal API for C and Python.
    It provides access to internal Z3 components.
    It should only be used by advanced users.
    We used it to build regression tests in Python.

Author:

    Leonardo de Moura (leonardo) 2012-10-18

Notes:
    
--*/
#ifndef _Z3_INTERNAL_H_
#define _Z3_INTERNAL_H_

#include"z3_macros.h"
#include"z3_api.h"
#include"z3_internal_types.h"
#include"z3_poly.h"

#undef __in
#undef __out
#undef __inout
#undef __in_z
#undef __out_z
#undef __ecount
#undef __in_ecount
#undef __out_ecount
#undef __inout_ecount

#endif
