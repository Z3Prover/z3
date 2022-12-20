/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    propagate_ineqs_tactic.h
     
Author:

    Leonardo (leonardo) 2012-02-19

Tactic Documentation:

## Tactic propagate-ineqs

### Short Description

Propagate ineqs/bounds, remove subsumed inequalities

### Long Description

This tactic performs the following tasks:

- Propagate bounds using the bound_propagator.
- Eliminate subsumed inequalities.
  - For example:
    `x - y >= 3` can be replaced with true if we know that `x >= 3` and `y <= 0`

 - Convert inequalities of the form `p <= k` and `p >= k` into `p = k`,
   where `p` is a polynomial and `k` is a constant.

This strategy assumes the input is in arith LHS mode.
This can be achieved by using option :arith-lhs true in the simplifier.

### Example
```z3
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const u Int)
(declare-const v Int)
(declare-const w Int)
(assert (>= x 3))
(assert (<= y 0))
(assert (>= (- x y) 3))
(assert (>= (* u v w) 2))
(assert (<= (* v u w) 2))
(apply (and-then simplify propagate-ineqs))
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_propagate_ineqs_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("propagate-ineqs", "propagate ineqs/bounds, remove subsumed inequalities.", "mk_propagate_ineqs_tactic(m, p)")
*/

