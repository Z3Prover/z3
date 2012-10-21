/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    shallow_context_simplifier.h

Abstract:

    Depth 1 context simplifier.

Author:

    Leonardo de Moura (leonardo) 2011-04-28


Revision History:

--*/
#ifndef _SHALLOW_CONTEXT_SIMPLIFIER_H_
#define _SHALLOW_CONTEXT_SIMPLIFIER_H_

#include"assertion_set_strategy.h"

class shallow_context_simplifier : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    shallow_context_simplifier(ast_manager & m, params_ref const & p = params_ref());
    virtual ~shallow_context_simplifier();

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }

    void operator()(assertion_set & s);

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        operator()(s);
        mc = 0;
    }

    virtual void cleanup();

    unsigned get_num_steps() const;
protected:
    virtual void set_cancel(bool f);
};

inline as_st * mk_shallow_simplifier(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(shallow_context_simplifier, m, p));
}

inline as_st * mk_constant_propagation(ast_manager & m, params_ref const & p = params_ref()) {
    return mk_shallow_simplifier(m, p);
}

#endif
