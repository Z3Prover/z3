/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    theory_bv_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include"theory_bv_params.h"
#include"smt_params_helper.hpp"

void theory_bv_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_bv_reflect = p.bv_reflect();
    m_bv_enable_int2bv2int = p.bv_enable_int2bv(); 
}
