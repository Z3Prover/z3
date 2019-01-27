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

#include "model/model.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include "util/event_handler.h"
#include "tactic/model_converter.h"

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
    model_converter_ref m_mc0;
public:
    check_sat_result():m_ref_count(0), m_status(l_undef) {}
    virtual ~check_sat_result() {}
    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }
    lbool set_status(lbool r) { return m_status = r; }
    lbool status() const { return m_status; }
    virtual void collect_statistics(statistics & st) const = 0;
    virtual void get_unsat_core(expr_ref_vector & r) = 0;
    void set_model_converter(model_converter* mc) { m_mc0 = mc; }
    model_converter* mc0() const { return m_mc0.get(); }
    virtual void get_model_core(model_ref & m) = 0;
    void get_model(model_ref & m) {
        get_model_core(m);
        if (m && mc0()) (*mc0())(m);
    }
    virtual proof * get_proof() = 0;
    virtual std::string reason_unknown() const = 0;
    virtual void set_reason_unknown(char const* msg) = 0;
    void set_reason_unknown(event_handler& eh);
    virtual void get_labels(svector<symbol> & r) = 0;
    virtual ast_manager& get_manager() const = 0;

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
    ~simple_check_sat_result() override;
    ast_manager& get_manager() const override { return m_proof.get_manager(); }
    void collect_statistics(statistics & st) const override;
    void get_unsat_core(expr_ref_vector & r) override;
    void get_model_core(model_ref & m) override;
    proof * get_proof() override;
    std::string reason_unknown() const override;
    void get_labels(svector<symbol> & r) override;
    void set_reason_unknown(char const* msg) override { m_unknown = msg; }
};

#endif
