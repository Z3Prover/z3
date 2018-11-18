/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    check_sat_result.cpp

Abstract:
    Abstract interface for storing the result produced by 
    a check_sat like command

Author:

    Leonardo (leonardo) 2012-11-01

Notes:

--*/
#include "solver/check_sat_result.h"

void check_sat_result::set_reason_unknown(event_handler& eh) {
    switch (eh.caller_id()) {
    case UNSET_EH_CALLER: break;
    case CTRL_C_EH_CALLER:
        set_reason_unknown("interrupted from keyboard");
        break;
    case TIMEOUT_EH_CALLER:
        set_reason_unknown("timeout");
        break;
    case RESLIMIT_EH_CALLER:
        set_reason_unknown("max. resource limit exceeded");
        break;
    case API_INTERRUPT_EH_CALLER:
        set_reason_unknown("interrupted");
        break;
    }
}


simple_check_sat_result::simple_check_sat_result(ast_manager & m):
    m_core(m),
    m_proof(m) {
    }

simple_check_sat_result::~simple_check_sat_result() {
}

void simple_check_sat_result::collect_statistics(statistics & st) const { 
    st.copy(m_stats); 
}

void simple_check_sat_result::get_unsat_core(expr_ref_vector & r) { 
    if (m_status == l_false) {
        r.reset();
        r.append(m_core.size(), m_core.c_ptr()); 
    }
}
 
void simple_check_sat_result::get_model_core(model_ref & m) { 
    if (m_status != l_false) 
        m = m_model; 
    else 
        m = nullptr;
}

proof * simple_check_sat_result::get_proof() { 
    return m_status == l_false ? m_proof.get() : nullptr;
}

std::string simple_check_sat_result::reason_unknown() const { 
    return m_unknown; 
}

void simple_check_sat_result::get_labels(svector<symbol> & r) {
}
