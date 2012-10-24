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

#include"ini_file.h"

struct bv_simplifier_params {
    bool  m_hi_div0; //!< if true, uses the hardware interpretation for div0, mod0, ... if false, div0, mod0, ... are considered uninterpreted.
    bool  m_bv2int_distribute; //!< if true allows downward propagation of bv2int.

    bv_simplifier_params():
        m_hi_div0(true),
        m_bv2int_distribute(true) {
    }
    void register_params(ini_params & p) {
        p.register_bool_param("HI_DIV0", m_hi_div0, "if true, then Z3 uses the usual hardware interpretation for division (rem, mod) by zero. Otherwise, these operations are considered uninterpreted.");
        p.register_bool_param("BV2INT_DISTRIBUTE", m_bv2int_distribute, "if true, then int2bv is distributed over arithmetical operators.");
    }
};

#endif /* _BV_SIMPLIFIER_PARAMS_H_ */

