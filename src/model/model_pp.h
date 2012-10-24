/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_pp.h

Abstract:

    Pretty printer for models for debugging purposes.

Author:

    Leonardo de Moura (leonardo)

Revision History:


--*/
#ifndef _MODEL_PP_H_
#define _MODEL_PP_H_

#include<iostream>
class model_core;

void model_pp(std::ostream & out, model_core const & m);

#endif
