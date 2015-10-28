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
#include"bv_rewriter_params.hpp"

void bv_simplifier_params::updt_params(params_ref const & _p) {
    bv_simplifier_params_helper p(_p);
    bv_rewriter_params rp(_p);
    m_hi_div0 = rp.hi_div0();
    m_bv2int_distribute = p.bv_bv2int_distribute();

}
