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
#ifndef CTX_SIMPLIFY_TACTIC_H_
#define CTX_SIMPLIFY_TACTIC_H_

#include"tactical.h"
#include"goal_num_occurs.h"

class ctx_simplify_tactic : public tactic {
public:
    class simplifier {
        goal_num_occurs* m_occs;
    public:
        virtual ~simplifier() {}
        virtual bool assert_expr(expr * t, bool sign) = 0;
        virtual bool simplify(expr* t, expr_ref& result) = 0;
        virtual bool may_simplify(expr* t) { return true; }
        virtual void pop(unsigned num_scopes) = 0;
        virtual simplifier * translate(ast_manager & m) = 0;
        virtual unsigned scope_level() const = 0;
        virtual void updt_params(params_ref const & p) {}
        void set_occs(goal_num_occurs& occs) { m_occs = &occs; };
        bool shared(expr* t) const;
    };
    
protected:
    struct      imp;
    imp *       m_imp;
    params_ref  m_params;
public:
    ctx_simplify_tactic(ast_manager & m, simplifier* simp, params_ref const & p = params_ref());

    virtual tactic * translate(ast_manager & m);

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
};

tactic * mk_ctx_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("ctx-simplify", "apply contextual simplification rules.", "mk_ctx_simplify_tactic(m, p)")
*/

#endif
