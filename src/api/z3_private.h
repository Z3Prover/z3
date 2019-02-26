/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    z3_private.h

Abstract:

    Z3 API.

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2007-06-8

Notes:

--*/

#include<iostream>
#include "util/rational.h"
#include "api/z3_macros.h"

#ifndef Z3_PRIVATE_H_
#define Z3_PRIVATE_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    bool Z3_API Z3_get_numeral_rational(Z3_context c, Z3_ast a, rational& r);

#ifdef __cplusplus
};
#endif // __cplusplus

#endif

