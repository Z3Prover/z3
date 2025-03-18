/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    simplify_tactic.h

Abstract:

    Apply simplification and rewriting rules.

Author:

    Leonardo (leonardo) 2011-11-20

Tactic Documentation:

## Tactic simplify

### Short Description:

The tactic performs algebraic simplifications on formulas

### Long Description

The simplify tactic invokes z3's main rewriting engine. 
The rewriting engine contains support for theory specific simplifications.
The set of simplifications invoked is open ended. Useful algebraic simplifications
are added to the rewrite engine as they are discovered to be useful.

Note that the simplifier does not ensure that equivalent formulas are simplified to the same form.
In other words it does not guarantee canonicity. This contrasts with BDD packages where BDDs constructed
from two equivalent formulas are guaranteed to be equal.

### Example
 
```z3
  (declare-const x Int)
  (declare-const y Int)
  (assert (> x (+ x y)))
  (apply simplify)
```

The simplifier is also exposed as a stand-alone command.
There are several options to control its behavior.

```z3
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const u Int)
(declare-fun p (Int) Bool)
(assert (p (* (+ x y) (+ z u))))
(apply simplify)
(apply (with simplify :som true))

(simplify (* (+ x y) (+ z u)) :som false)
(simplify (* (+ x y) (+ z u)) :som true)
```

### Notes

* supports unsat cores, proof terms

--*/
#pragma once

#include "tactic/tactic.h"
#include "tactic/tactical.h"

class simplify_tactic : public tactic {
    bool       m_clean = true;
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    simplify_tactic(ast_manager & m, params_ref const & ref = params_ref());
    ~simplify_tactic() override;

    void updt_params(params_ref const & p) override;

    static void get_param_descrs(param_descrs & r);
    
    void collect_param_descrs(param_descrs & r) override { get_param_descrs(r); }

    void collect_statistics(statistics& st) const override;
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override;
    
    void cleanup() override;

    unsigned get_num_steps() const;

    tactic * translate(ast_manager & m) override { return alloc(simplify_tactic, m, m_params); }

    char const* name() const override { return "simplify"; }

};

tactic * mk_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_elim_and_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("simplify", "apply simplification rules.", "mk_simplify_tactic(m, p)")
  ADD_TACTIC("elim-and", "convert (and a b) into (not (or (not a) (not b))).", "mk_elim_and_tactic(m, p)")
*/

