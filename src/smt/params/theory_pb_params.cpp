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
#include "smt/params/theory_pb_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_pb_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_pb_conflict_frequency = p.pb_conflict_frequency();
    m_pb_learn_complements = p.pb_learn_complements();
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void theory_pb_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_pb_conflict_frequency);
    DISPLAY_PARAM(m_pb_learn_complements);
}
