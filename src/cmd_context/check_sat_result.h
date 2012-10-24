/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    check_sat_result.h

Abstract:
    Abstract interface for storing the result produced by 
    a check_sat like command

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#ifndef _CHECK_SAT_RESULT_H_
#define _CHECK_SAT_RESULT_H_

#include"model.h"
#include"lbool.h"
#include"statistics.h"

class check_sat_result {
protected:
    unsigned    m_ref_count;
    lbool       m_status; 
public:
    check_sat_result():m_ref_count(0), m_status(l_undef) {}
    virtual ~check_sat_result() {}
    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }
    void set_status(lbool r) { m_status = r; }
    lbool status() const { return m_status; }
    virtual void collect_statistics(statistics & st) const = 0;
    virtual void get_unsat_core(ptr_vector<expr> & r) = 0;
    virtual void get_model(model_ref & m) = 0;
    virtual proof * get_proof() = 0;
    virtual std::string reason_unknown() const = 0;
    virtual void get_labels(svector<symbol> & r) = 0;
};

struct simple_check_sat_result : public check_sat_result {
    statistics      m_stats;
    model_ref       m_model;
    expr_ref_vector m_core;
    proof_ref       m_proof;
    std::string     m_unknown;

    simple_check_sat_result(ast_manager & m):
        m_core(m),
        m_proof(m) {
    }
    virtual ~simple_check_sat_result() {}
    virtual void collect_statistics(statistics & st) const { st.copy(m_stats); }
    virtual void get_unsat_core(ptr_vector<expr> & r) { if (m_status == l_false) r.append(m_core.size(), m_core.c_ptr()); }
    virtual void get_model(model_ref & m) { 
        if (m_status != l_false) m = m_model; else m = 0; 
    }
    virtual proof * get_proof() { return m_status == l_false ? m_proof.get() : 0; }
    virtual std::string reason_unknown() const { 
        return m_unknown; 
    }
    virtual void get_labels(svector<symbol> & r) {}
};

#endif
