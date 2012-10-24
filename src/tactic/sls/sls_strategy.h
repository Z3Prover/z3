/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sls_strategy.h

Abstract:

    A Stochastic Local Search (SLS) strategy 

Author:

    Christoph (cwinter) 2011-09-23

Notes:

--*/
#ifndef _SLS_STRATEGY_H_
#define _SLS_STRATEGY_H_

#include"assertion_set_strategy.h"

MK_ST_EXCEPTION(sls_exception);

class sls_st : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    sls_st(ast_manager & m, params_ref const & p = params_ref());
    virtual ~sls_st();

    ast_manager & m () const;

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }

    bool is_target(assertion_set const & s) const;
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc);
    
    virtual void cleanup();
        
    virtual void collect_statistics(statistics & st) const;
    virtual void reset_statistics();
protected:
    virtual void set_cancel(bool f);
};

inline as_st * mk_sls(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(sls_st, m, p));
}


as_st * mk_qfbv_sls_strategy(ast_manager & m, params_ref const & p);

MK_SIMPLE_ST_FACTORY(qfbv_sls_stf, mk_qfbv_sls_strategy(m, p));

#endif
