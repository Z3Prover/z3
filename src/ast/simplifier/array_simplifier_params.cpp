/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    array_simplifier_params.cpp

Abstract:

    This file was created during code reorg.

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include"array_simplifier_params.h"
#include"array_simplifier_params_helper.hpp"

void array_simplifier_params::updt_params(params_ref const & _p) {
    array_simplifier_params_helper p(_p);
    m_array_canonize_simplify = p.array_canonize();
    m_array_simplify          = p.array_simplify();
}
