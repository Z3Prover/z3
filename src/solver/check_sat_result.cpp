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

void check_sat_result::set_reason_unknown(event_handler& eh, char const* what) {
    switch (eh.caller_id()) {
    case UNSET_EH_CALLER: 
        if (reason_unknown() == "")
            set_reason_unknown(what);
        break;
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

void check_sat_result::set_reason_unknown(event_handler& eh, std::exception& ex) {
    switch (eh.caller_id()) {
    case UNSET_EH_CALLER: 
        if (reason_unknown() == "")
            set_reason_unknown(ex.what());
        break;
    default:
        set_reason_unknown(eh, ex.what());
        break;
    }
}

proof* check_sat_result::get_proof() {
    if (!m_log.empty() && !m_proof) {
        SASSERT(is_app(m_log.back()));
        app* last = to_app(m_log.back());
        expr* fact = m.get_fact(last);
        m_log.push_back(fact);
        m_proof = m.mk_clause_trail(m_log.size(), m_log.data());            
    }
    if (m_proof)
        return m_proof.get();
    return get_proof_core();
}

simple_check_sat_result::simple_check_sat_result(ast_manager & m):
    check_sat_result(m),
    m_core(m),
    m_proof(m) {
    }

void simple_check_sat_result::collect_statistics(statistics & st) const { 
    st.copy(m_stats); 
}

void simple_check_sat_result::get_unsat_core(expr_ref_vector & r) { 
    if (m_status == l_false) {
        r.reset();
        r.append(m_core.size(), m_core.data()); 
    }
}
 
void simple_check_sat_result::get_model_core(model_ref & m) { 
    if (m_status != l_false) 
        m = m_model; 
    else 
        m = nullptr;
}

proof * simple_check_sat_result::get_proof_core() { 
    return m_proof;
}

std::string simple_check_sat_result::reason_unknown() const { 
    return m_unknown; 
}

void simple_check_sat_result::get_labels(svector<symbol> & r) {
}
