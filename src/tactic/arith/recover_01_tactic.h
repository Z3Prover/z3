/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    recover_01_tactic.h

Author:

    Leonardo de Moura (leonardo) 2012-02-17.

Tactic Documentation:

## Tactic recover-01

### Short Description

Recover 01 variables from propositional constants.

### Long Description

Search for clauses of the form

```
    p  or q or  x = 0
    ~p or q or  x = k1
    p  or ~q or x = k2
    ~p or ~q or x = k1+k2
```

Then, replaces 


* `x` with `k1*y1 + k2*y2`
* `p` with `y1 = 1`
* `q` with `y2 = 1`

where `y1` and `y2` are fresh 01 variables.

The clauses are also removed.

### Example

```z3
(declare-const p Bool)
(declare-const q Bool)
(declare-const x Int)
(assert (or p q (= x 0)))
(assert (or (not p) q (= x 3)))
(assert (or p (not q) (= x 6)))
(assert (or (not p) (not q) (= x 9)))
(apply recover-01)
```

### Notes

* does not support proofs, does not support cores

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_recover_01_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("recover-01", "recover 0-1 variables hidden as Boolean variables.", "mk_recover_01_tactic(m, p)")
*/

