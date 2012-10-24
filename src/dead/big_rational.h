/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    big_rational.h

Abstract:

    Big rational numbers

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

Revision History:

--*/
#ifndef _BIG_RATIONAL_H_
#define _BIG_RATIONAL_H_

#ifdef _WINDOWS
#include"..\msbig_rational\msbig_rational.h"
#else
#ifdef NO_GMP
#include"dummy_big_rational.h"
#else
#include"gmp_big_rational.h"
#endif
#endif

#endif /* _BIG_RATIONAL_H_ */

