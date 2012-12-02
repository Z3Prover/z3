/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array_simplifier_params.h

Abstract:

    This file was created during code reorg.

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#ifndef _ARRAY_SIMPLIFIER_PARAMS_H_
#define _ARRAY_SIMPLIFIER_PARAMS_H_

#include"array_simplifier_params_helper.hpp"

struct array_simplifier_params {
    bool            m_array_canonize_simplify;
    bool            m_array_simplify; // temporary hack for disabling array simplifier plugin.

    array_simplifier_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & _p) {
        array_simplifier_params_helper p(_p);
        m_array_canonize_simplify = p.array_canonize();
        m_array_simplify          = p.array_simplify();
    }
};
    
#endif /* _ARITH_SIMPLIFIER_PARAMS_H_ */

