/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    lia2card_tactic.h

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-5

Tactic Documentation:

## Tactic lia2card

### Short Description

Extract 0-1 integer variables used in 
cardinality and pseudo-Boolean constraints and replace them by Booleans.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (<= 0 x))
(assert (<= 0 y))
(assert (<= 0 z))
(assert (>= 1 x))
(assert (>= 1 y))
(assert (>= 1 z))
(assert (>= (+ (* 5 x) (* -2 z) (* 3 y) 1) 4))
(apply lia2card)
```

### Notes

* The tactic does not (properly) support proofs or cores.

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_lia2card_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("lia2card", "introduce cardinality constraints from 0-1 integer.", "mk_lia2card_tactic(m, p)")
*/

bool get_pb_sum(expr* term, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff);

