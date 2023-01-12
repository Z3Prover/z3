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

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_snf_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_nnf_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("snf", "put goal in skolem normal form.", "mk_snf_tactic(m, p)")
  ADD_TACTIC("nnf", "put goal in negation normal form.", "mk_nnf_tactic(m, p)")
*/


