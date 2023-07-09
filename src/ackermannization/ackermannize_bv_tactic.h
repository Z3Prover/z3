/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

ackermannize_bv_tactic.h

Abstract:

Author:

Mikolas Janota

Tactic Documentation:

## Tactic ackernannize_bv

### Short Description

A tactic for performing Ackermann reduction for bit-vector formulas

### Long Description

The Ackermann reduction replaces uninterpreted functions $f(t_1), f(t_2)$
by fresh variables $f_1, f_2$ and adds axioms $t_1 \simeq t_2 \implies f_1 \simeq f_2$.
The reduction has the effect of eliminating uninterpreted functions. When the reduction
produces a pure bit-vector benchmark, it allows Z3 to use a specialized SAT solver.

### Example

```z3
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-fun f ((_ BitVec 32)) (_ BitVec 8))

(assert (not (= (f x) (f y))))
(apply ackermannize_bv)
```

### Notes

* does not support proofs, does not support unsatisfiable cores


--*/

#pragma once
#include "tactic/tactical.h"

tactic * mk_ackermannize_bv_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("ackermannize_bv", "A tactic for performing full Ackermannization on bv instances.", "mk_ackermannize_bv_tactic(m, p)")
*/


