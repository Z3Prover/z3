/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    add_bounds.h

Abstract:

    Strategy for bounding unbounded variables.

Author:

    Leonardo de Moura (leonardo) 2011-06-30.

Revision History:

--*/
#ifndef _ADD_BOUNDS_H_
#define _ADD_BOUNDS_H_

#include"assertion_set_strategy.h"

bool is_unbounded(assertion_set const & s);

class add_bounds : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    add_bounds(ast_manager & m, params_ref const & p = params_ref());
    virtual ~add_bounds();

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }

    virtual void operator()(assertion_set & s, model_converter_ref & mc);
    
    virtual void cleanup();

protected:
    virtual void set_cancel(bool f);
};

inline as_st * mk_add_bounds(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(add_bounds, m, p));
}

#endif
