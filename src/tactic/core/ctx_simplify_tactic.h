/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ctx_simplify_tactic.h

Abstract:

    Simple context simplifier for propagating constants.

Author:

    Leonardo (leonardo) 2011-10-26

Notes:

--*/
#ifndef _CTX_SIMPLIFY_TACTIC_H_
#define _CTX_SIMPLIFY_TACTIC_H_

#include"tactical.h"

class ctx_simplify_tactic : public tactic {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    ctx_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());

    virtual tactic * translate(ast_manager & m) {
        return alloc(ctx_simplify_tactic, m, m_params);
    }

    virtual ~ctx_simplify_tactic();

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core);

    virtual void cleanup();
protected:
    virtual void set_cancel(bool f);
};

inline tactic * mk_ctx_simplify_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return clean(alloc(ctx_simplify_tactic, m, p));
}

/*
  ADD_TACTIC("ctx-simplify", "apply contextual simplification rules.", "mk_ctx_simplify_tactic(m, p)")
*/

#endif
