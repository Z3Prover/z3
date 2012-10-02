/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_term_ite_strategy.h

Abstract:

    Eliminate term if-then-else by adding 
    new fresh auxiliary variables.

Author:

    Leonardo (leonardo) 2011-06-15

Notes:

--*/
#ifndef _ELIM_TERM_ITE_STRATEGY_H_
#define _ELIM_TERM_ITE_STRATEGY_H_

#include"strategy_exception.h"
#include"model_converter.h"
#include"params.h"
#include"assertion_set_strategy.h"

class assertion_set;
MK_ST_EXCEPTION(elim_term_ite_exception);

class elim_term_ite_strategy : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    elim_term_ite_strategy(ast_manager & m, params_ref const & p = params_ref());
    virtual ~elim_term_ite_strategy();

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc);

    virtual void cleanup();
    virtual void set_cancel(bool f);
};

inline as_st * mk_elim_term_ite(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(elim_term_ite_strategy, m, p));
}

#endif
