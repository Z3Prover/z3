/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bv_simplifier_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-10.

Revision History:

--*/
#ifndef _BV_SIMPLIFIER_PARAMS_H_
#define _BV_SIMPLIFIER_PARAMS_H_

#include"params.h"

struct bv_simplifier_params {
    bool  m_hi_div0; //!< if true, uses the hardware interpretation for div0, mod0, ... if false, div0, mod0, ... are considered uninterpreted.
    bool  m_bv2int_distribute; //!< if true allows downward propagation of bv2int.

    bv_simplifier_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & _p);
};

#endif /* _BV_SIMPLIFIER_PARAMS_H_ */

