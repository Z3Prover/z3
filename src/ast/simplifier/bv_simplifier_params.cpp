/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bv_simplifier_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include"bv_simplifier_params.h"
#include"bv_simplifier_params_helper.hpp"

void bv_simplifier_params::updt_params(params_ref const & _p) {
    bv_simplifier_params_helper p(_p);
    m_hi_div0 = p.bv_hi_div0();
    m_bv2int_distribute = p.bv_bv2int_distribute();
}
