/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nnf_tactic.h

Abstract:

    NNF tactic

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Note:

   tactic documentation below co-created using gptchat (with some corrections) :-)

Tactic Documentation:

## Tactic nnf

### Short Description:

The tactic converts formulas to negation normal form (NNF)

### Long Description

In NNF, negations only appear in front of atomic formulas. 

Standard rules for conversion into negation normal form are:
- `(not (and p q))` is converted to `(or (not p) (not q))`
- `(not (or p q))` is converted to `(and (not p) (not q))`
- `(not (not p))` is converted to `p`
- `(not (exists x. p))` is converted to `(forall x. (not p))`
- `(not (forall x. p))` is converted to `(exists x. (not p))`


Once all negations are pushed inside, the resulting formula is in NNF.

### Example

```z3
  (declare-const x Int)
  (assert (not (or (> x 0) (< x 0))))
  (apply nnf)
```


### Notes

* supports unsat cores, proof terms



--*/
#pragma once

#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/nnf_simplifier.h"

inline tactic * mk_snf_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(nnf_simplifier, m, p, s);
        });
}

inline tactic * mk_nnf_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    params_ref new_p(p);
    new_p.set_sym("mode", symbol("full"));
    return using_params(mk_snf_tactic(m, new_p), new_p);
}

/*
  ADD_TACTIC("snf", "put goal in skolem normal form.", "mk_snf_tactic(m, p)")
  ADD_TACTIC("nnf", "put goal in negation normal form.", "mk_nnf_tactic(m, p)")
  ADD_SIMPLIFIER("nnf", "put formula in negation normal form.", "alloc(nnf_simplifier, m, p, s)")
*/


