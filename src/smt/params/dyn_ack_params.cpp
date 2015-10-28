/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dyn_ack_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-05-18.

Revision History:

--*/
#include"dyn_ack_params.h"
#include"smt_params_helper.hpp"

void dyn_ack_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_dack = static_cast<dyn_ack_strategy>(p.dack());
    m_dack_eq = p.dack_eq();
    m_dack_factor = p.dack_factor();
    m_dack_threshold = p.dack_threshold();
    m_dack_gc = p.dack_gc();
    m_dack_gc_inv_decay = p.dack_gc_inv_decay();
}
