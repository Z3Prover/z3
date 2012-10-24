/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_simplifier_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-09.

Revision History:

--*/

#include"arith_simplifier_params.h"

void arith_simplifier_params::register_params(ini_params & p) {
    p.register_bool_param("ARITH_EXPAND_EQS", m_arith_expand_eqs);
    p.register_bool_param("ARITH_PROCESS_ALL_EQS", m_arith_process_all_eqs);
}

