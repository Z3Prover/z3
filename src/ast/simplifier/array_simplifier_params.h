/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    array_simplifier_params.h

Abstract:

    This file was created during code reorg.

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#ifndef ARRAY_SIMPLIFIER_PARAMS_H_
#define ARRAY_SIMPLIFIER_PARAMS_H_

#include "util/params.h"

struct array_simplifier_params1 {

    array_simplifier_params1(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & _p);
};
    
#endif /* ARITH_SIMPLIFIER_PARAMS_H_ */

