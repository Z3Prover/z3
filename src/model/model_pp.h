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
#pragma once

#include<iostream>
class model_core;

void model_pp(std::ostream & out, model_core const & m);

