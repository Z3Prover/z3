/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    diff_neq_tactic.h

Author:

    Leonardo de Moura (leonardo) 2012-02-07.

Tactic Documentation:

## Tactic diff-neq

### Short Description

A specialized solver for integer problems using only constant bounds and differences to constants.

### Long Description

Solver for integer problems that contains literals of the form
```
       k <= x
       x <= k
       x - y != k
```

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= x 1))
(assert (<= 0 y))
(assert (<= y 1))
(assert (not (= (+ x (* -1 y)) -1)))
(assert (not (= (+ x (* -1 y)) 1)))
(assert (not (= (+ x (* -1 y)) 0)))
(apply diff-neq)
```

### Notes

* The tactic works only when the lower bounds are 0 and disequalities use multiplication with -1. Use normalize-bounds to ensure all lower bounds are 0.

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_diff_neq_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("diff-neq", "specialized solver for integer arithmetic problems that contain only atoms of the form (<= k x) (<= x k) and (not (= (- x y) k)), where x and y are constants and k is a numeral, and all constants are bounded.", "mk_diff_neq_tactic(m, p)")
*/
