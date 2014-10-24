/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-06.

Revision History:

--*/
#include"theory_array_params.h"
#include"smt_params_helper.hpp"

void theory_array_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_array_weak = p.array_weak();
    m_array_extensional = p.array_extensional();
}


