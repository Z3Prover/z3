/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    z3_logger.h

Abstract:

    Goodies for log generation

Author:

    Leonardo de Moura (leonardo) 2011-09-22

Notes:
    
--*/
#pragma once

#include "util/symbol.h"

void R();
void P(void * obj);
void I(int64_t i);
void U(uint64_t u);
void D(double d);
void S(Z3_string str);
void Sy(Z3_symbol sym);
void Ap(unsigned sz);
void Au(unsigned sz);
void Ai(unsigned sz);
void Asy(unsigned sz);
void C(unsigned id);
