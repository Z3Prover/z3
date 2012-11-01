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
#include"check_sat_result.h"

simple_check_sat_result::simple_check_sat_result(ast_manager & m):
    m_core(m),
    m_proof(m) {
    }

simple_check_sat_result::~simple_check_sat_result() {
}

void simple_check_sat_result::collect_statistics(statistics & st) const { 
    st.copy(m_stats); 
}

void simple_check_sat_result::get_unsat_core(ptr_vector<expr> & r) { 
    if (m_status == l_false) 
        r.append(m_core.size(), m_core.c_ptr()); 
}
 
void simple_check_sat_result::get_model(model_ref & m) { 
    if (m_status != l_false) 
        m = m_model; 
    else 
        m = 0; 
}

proof * simple_check_sat_result::get_proof() { 
    return m_status == l_false ? m_proof.get() : 0; 
}

std::string simple_check_sat_result::reason_unknown() const { 
    return m_unknown; 
}

void simple_check_sat_result::get_labels(svector<symbol> & r) {
}
