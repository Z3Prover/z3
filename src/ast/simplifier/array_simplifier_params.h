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

struct array_simplifier_params {
    bool            m_array_canonize_simplify;
    bool            m_array_simplify; // temporary hack for disabling array simplifier plugin.

    array_simplifier_params():
        m_array_canonize_simplify(false),
        m_array_simplify(true) {
    }
};
    
#endif /* _ARITH_SIMPLIFIER_PARAMS_H_ */

