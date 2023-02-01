/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    degree_shift_tactic.h

Author:

    Leonardo de Moura (leonardo) 2011-12-30.

Tactic Documentation:

## Tactic degree-shift

### Short Description

The procedure reduces the degrees of variables.

### Long Description
    
Basic idea: if goal $G$ contains a real variable $x$, $x$ occurs with degrees
$d_1, ..., d_k$ in $G$, and $n = \gcd(d_1, ..., d_k) > 1$.
Then, replace $x^n$ with a new fresh variable $y$.

### Example

```z3
(declare-const x Real)
(declare-const y Real)
(assert (> (+ (* x x x 4) (* x x 3)) 0))
(assert (= (* x x) (* y y)))
(apply degree-shift)
```

### Notes

* supports proofs and cores

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_degree_shift_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("degree-shift", "try to reduce degree of polynomials (remark: :mul2power simplification is automatically applied).", "mk_degree_shift_tactic(m, p)")
*/

