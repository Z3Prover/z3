/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_v2_pp.h

Abstract:

    V2 Pretty printer for models. (backward compatibility)

Author:

    Leonardo de Moura (leonardo)

Revision History:
--*/
#ifndef MODEL_V2_PP_H_
#define MODEL_V2_PP_H_

#include<iostream>
class model_core;

void model_v2_pp(std::ostream & out, model_core const & m, bool partial = false);

#endif
