/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include"smt_params.h"
#include"smt_params_helper.hpp"

void smt_params::updt_local_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_auto_config = p.auto_config();
    m_ematching   = p.ematching();
    m_phase_selection = static_cast<phase_selection>(p.phase_selection());
    m_restart_strategy = static_cast<restart_strategy>(p.restart_strategy());
    m_restart_factor = p.restart_factor();
    m_case_split_strategy = static_cast<case_split_strategy>(p.case_split());
    m_delay_units = p.delay_units();
    m_delay_units_threshold = p.delay_units_threshold();
}

void smt_params::updt_params(params_ref const & p) {
    preprocessor_params::updt_params(p);
    qi_params::updt_params(p);
    theory_arith_params::updt_params(p);
    theory_bv_params::updt_params(p);
    updt_local_params(p);
}

void smt_params::updt_params(context_params const & p) {
    m_auto_config    = p.m_auto_config;
    m_soft_timeout   = p.m_timeout;
    m_model          = p.m_model;
    m_model_validate = p.m_validate_model;
    m_proof_mode     = p.m_proof ? PGM_FINE : PGM_DISABLED;
}

