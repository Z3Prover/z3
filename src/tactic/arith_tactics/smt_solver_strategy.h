/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_solver_strategy.h

Abstract:

    Strategy for using the SAT solver.

Author:

    Leonardo (leonardo) 2011-06-25

Notes:

--*/
#ifndef _SMT_SOLVER_STRATEGY_H_
#define _SMT_SOLVER_STRATEGY_H_

#include"assertion_set_strategy.h"

namespace smt { class solver_exp; };

class smt_solver_strategy : public assertion_set_strategy {
    struct imp;
    ast_manager &               m;
    params_ref                  m_params;
    statistics                  m_stats;
    scoped_ptr<smt::solver_exp> m_solver;
    void init_solver();
public:
    smt_solver_strategy(ast_manager & m, params_ref const & p = params_ref());
    virtual ~smt_solver_strategy();

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

inline as_st * mk_smt2_solver(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(smt_solver_strategy, m, p));
}

#endif
