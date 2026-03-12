/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    injectivity_tactic.h

Abstract:

    Injectivity tactics

Author:

    Nicolas Braud-Santoni (t-nibrau) 2017-08-10


Tactic Documentation:

## Tactic injectivity

### Short Description:

- Discover axioms of the form `forall x. (= (g (f x)) x`
  Mark `f` as injective

- Rewrite (sub)terms of the form `(= (f x) (f y))` to `(= x y)` whenever `f` is injective.

### Example
 
```z3
  (declare-fun f (Int) Int)
  (declare-fun g (Int) Int)
  (declare-const x Int)
  (declare-const y Int)
  (assert (forall ((x Int)) (= (g (f x)) x)))
  (assert (not (= (f x) (f (f y)))))
  (apply injectivity)
```

### Notes

* does not support cores nor proofs

--*/
#pragma once

#include "util/params.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/injectivity_simplifier.h"
class ast_manager;
class tactic;

tactic * mk_injectivity_tactic(ast_manager & m, params_ref const & p = params_ref());

inline tactic* mk_injectivity2_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(injectivity_simplifier, m, p, s);
        });
}

/*
  ADD_TACTIC("injectivity",  "Identifies and applies injectivity axioms.", "mk_injectivity_tactic(m, p)")
  ADD_TACTIC("injectivity2", "Identifies and applies injectivity axioms.", "mk_injectivity2_tactic(m, p)")
  ADD_SIMPLIFIER("injectivity", "Identifies and applies injectivity axioms.", "alloc(injectivity_simplifier, m, p, s)")
*/

