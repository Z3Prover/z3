/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    iz3exception.h

Abstract:

    Base class for exceptions raised by interpolation routines 

Author:

Notes:

--*/
#ifndef _IZ3EXCEPTION_H_
#define _IZ3EXCEPTION_H_

#include "z3_exception.h"
#include "error_codes.h"

class iz3_exception: public default_exception {
public:
    iz3_exception(const std::string &msg): default_exception(msg) {}
};

#endif
