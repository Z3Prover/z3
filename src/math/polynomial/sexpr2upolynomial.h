/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sexpr2upolynomial.h

Abstract:

    sexpr to upolynomial converter
    
Author:

    Leonardo (leonardo) 2011-12-28

Notes:

--*/
#ifndef _SEXPR2UPOLYNOMIAL_H_
#define _SEXPR2UPOLYNOMIAL_H_

#include"upolynomial.h"
#include"cmd_context_types.h"
class sexpr;

class sexpr2upolynomial_exception : public cmd_exception {
public:
    sexpr2upolynomial_exception(char const * msg, sexpr const * s);
};

void sexpr2upolynomial(upolynomial::manager & m, sexpr const * s, upolynomial::numeral_vector & p);

#endif
