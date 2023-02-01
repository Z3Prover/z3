/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    qe_tactic.h

Abstract:

    Quantifier elimination front-end for tactic framework.

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Tactic Documentation

## Tactic qe

### Short Description

Apply quantifier elimination on quantified sub-formulas.

### Long Description

The tactic applies quantifier elimination procedures on quantified sub-formulas.
It relies on theory plugins that can perform quanifier elimination for selected theories.
These plugins include Booleans, bit-vectors, arithmetic (linear), arrays, and data-types (term algebra).
It performs feasibility checks on cases to throttle the set of sub-formulas where quantifier elimination
is applied.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(assert (exists ((z Int)) (and (<= x (* 2 z)) (<= (* 3 z) y))))
(apply qe)
```

--*/

#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qe_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qe", "apply quantifier elimination.", "mk_qe_tactic(m, p)")
*/
