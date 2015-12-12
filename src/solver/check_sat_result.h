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
#ifndef CHECK_SAT_RESULT_H_
#define CHECK_SAT_RESULT_H_

#include"model.h"
#include"lbool.h"
#include"statistics.h"

/**
   \brief Abstract interface for the result of a (check-sat) like command.
   It encapsulates information such as:
      - the actual result: l_true (satisfiable), l_false (unsatisfiable), l_undef (unknown)
      - statistics
      - model (if the result is satisfiable)
      - proof (if the result is unsatisfiable)
      - unsat-core (if the result is unsatisfiable)
      - reason-unknown (if the result is unknown, i.e., the solver failed to solve the problem)
      - label (if the result is satisfiable) this is legacy for Boogie
      
*/
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
    virtual ast_manager& get_manager() = 0;
};

/**
   \brief Very simple implementation of the check_sat_result object.
*/
struct simple_check_sat_result : public check_sat_result {
    statistics      m_stats;
    model_ref       m_model;
    expr_ref_vector m_core;
    proof_ref       m_proof;
    std::string     m_unknown;
    

    simple_check_sat_result(ast_manager & m);
    virtual ~simple_check_sat_result();
    virtual ast_manager& get_manager() { return m_proof.get_manager(); }
    virtual void collect_statistics(statistics & st) const;
    virtual void get_unsat_core(ptr_vector<expr> & r);
    virtual void get_model(model_ref & m);
    virtual proof * get_proof();
    virtual std::string reason_unknown() const;
    virtual void get_labels(svector<symbol> & r);
};

#endif
