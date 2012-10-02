/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver_strategy.h

Abstract:

    Strategy for using the SAT solver.
    If the assertion set contains theory atoms, then the sat solver just
    checks whether the boolean abstraction is satisfiable or not.

Author:

    Leonardo (leonardo) 2011-06-02

Notes:

--*/
#ifndef _SAT_SOLVER_STRATEGY_H_
#define _SAT_SOLVER_STRATEGY_H_

#include"assertion_set_strategy.h"

class assertion_set;

class sat_solver_strategy : public assertion_set_strategy {
    struct imp;
    imp *      m_imp;
    params_ref m_params;
    statistics m_stats;
    struct scoped_set_imp;
public:
    sat_solver_strategy(ast_manager & m, params_ref const & p = params_ref());
    virtual ~sat_solver_strategy();

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc);

    virtual void cleanup();

    virtual void collect_statistics(statistics & st) const;
    virtual void reset_statistics();
protected:
    virtual void set_cancel(bool f);
};

inline as_st * mk_sat_solver(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(sat_solver_strategy, m, p));
}

// Apply only simplification procedures
inline as_st * mk_sat_preprocessor(ast_manager & m, params_ref const & p = params_ref()) {
    params_ref p_aux;
    p_aux.set_uint(":max-conflicts", 0);
    as_st * st = clean(using_params(mk_sat_solver(m), p_aux));
    st->updt_params(p);
    return st;
}

#endif
