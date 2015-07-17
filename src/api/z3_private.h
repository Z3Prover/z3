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
#include"rational.h"
#include"z3_macros.h"

#ifndef Z3_PRIVATE_H_
#define Z3_PRIVATE_H_


#ifndef CAMLIDL
#ifdef __cplusplus
extern "C" {
#endif // __cplusplus
#else
[pointer_default(ref)] interface Z3 {
#endif // CAMLIDL  

    Z3_bool Z3_API Z3_get_numeral_rational(Z3_context c, Z3_ast a, rational& r);

#ifndef CAMLIDL
#ifdef __cplusplus
};
#endif // __cplusplus
#else
}
#endif // CAMLIDL

#endif

