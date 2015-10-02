/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_pb_params.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2014-01-01

Revision History:

--*/
#include"theory_pb_params.h"
#include"smt_params_helper.hpp"

void theory_pb_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_pb_conflict_frequency = p.pb_conflict_frequency();
    m_pb_learn_complements = p.pb_learn_complements();
    m_pb_enable_compilation = p.pb_enable_compilation();
    m_pb_enable_simplex = p.pb_enable_simplex();
}
