/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cnf_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-23.

Revision History:

--*/

#include"cnf_params.h"

void cnf_params::register_params(ini_params & p) {
    p.register_unsigned_param("CNF_FACTOR", m_cnf_factor, "the maximum number of clauses that can be created when converting a subformula");
    p.register_int_param("CNF_MODE", 0, 3, reinterpret_cast<int&>(m_cnf_mode), "CNF translation mode: 0 - disabled, 1 - quantifiers in CNF, 2 - 0 + opportunistic, 3 - full");
}

