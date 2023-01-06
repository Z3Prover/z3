/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    occf_tactic.h

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Tactic Documentation:

## Tactic occf

### Short Description

Put goal in one constraint per clause normal form 

### Long Description

Put clauses in the assertion set in
OOC (one constraint per clause) form.
Constraints occurring in formulas that
are not clauses are ignored.
The formula can be put into CNF by
using `mk_sat_preprocessor` strategy.

### Example

```z3
(declare-const x Int)
(declare-const y Int)

(assert (or (= x y) (> x (- y))))
(assert (or (= x y) (< x (- y))))
(apply occf)
```

### Notes

* Does not support proofs
* only clauses are considered

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_occf_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("occf", "put goal in one constraint per clause normal form (notes: fails if proof generation is enabled; only clauses are considered).", "mk_occf_tactic(m, p)")
*/


