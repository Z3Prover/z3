/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ctx_simplify_tactic.h

Abstract:

    Simple context simplifier for propagating constants.

Author:

    Leonardo (leonardo) 2011-10-26

Tactic Documentation:

## Tactic ctx-simplify

### Short Description:

The tactic performs simplifies sub-formulas using context built up by walking assertions and sub-formulas.

### Example
 
```z3
  (declare-const p Bool)
  (declare-const q Bool)
  (declare-const r Bool)
  (declare-fun f (Bool) Bool)
  (assert p)
  (assert (or (f p) (and r (or (not r) q))))
  (apply ctx-simplify)
```

### Notes

* supports proof terms with limited features


--*/
#pragma once

#include "tactic/tactical.h"
#include "tactic/goal_num_occurs.h"

class ctx_simplify_tactic : public tactic {
public:
    class simplifier {
        goal_num_occurs* m_occs;
    public:
        virtual ~simplifier() = default;
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

    tactic * translate(ast_manager & m) override;

    ~ctx_simplify_tactic() override;

    char const* name() const override { return "ctx_simplify"; }

    void updt_params(params_ref const & p) override;
    static  void get_param_descrs(param_descrs & r);
    void collect_param_descrs(param_descrs & r) override { get_param_descrs(r); }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override;

    void cleanup() override;
};

tactic * mk_ctx_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("ctx-simplify", "apply contextual simplification rules.", "mk_ctx_simplify_tactic(m, p)")
*/

