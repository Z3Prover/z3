/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_simplifier_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include"arith_simplifier_params.h"
#include"arith_simplifier_params_helper.hpp"

void arith_simplifier_params::updt_params(params_ref const & _p) {
    arith_simplifier_params_helper p(_p);
    m_arith_expand_eqs      = p.arith_expand_eqs();
    m_arith_process_all_eqs = p.arith_process_all_eqs();
}
