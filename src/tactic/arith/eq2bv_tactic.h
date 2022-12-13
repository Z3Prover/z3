/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    eq2bv_tactic.h

Author:

    Nikolaj Bjorner (nbjorner) 2015-8-19

Tactic Documentation:

## Tactic eq2bv

### Short Description

Extract integer variables that are used as finite domain indicators.
The integer variables can only occur in equalities.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(assert (or (= x 5) (> y 3)))
(assert (or (= x 4) (= y 2)))
(apply eq2bv)
```

### Notes

* does not support proofs

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_eq2bv_tactic(ast_manager & m);

/*
    ADD_TACTIC("eq2bv", "convert integer variables used as finite domain elements to bit-vectors.", "mk_eq2bv_tactic(m)")
*/


