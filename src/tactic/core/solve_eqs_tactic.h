/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs_tactic.h

Abstract:

    Tactic for solving variables

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Tactic Documentation:

## Tactic solve-eqs

### Short Description

Solve for variables

### Long Description

The tactic eliminates variables that can be brought into solved form.
For example, the assertion `x = f(y + z)` can be solved for `x`, replacing `x`
everywhere by `f(x + y)`. It depends on a set of theory specific equality solvers

* Basic equations
  * equations between uninterpreted constants and terms. 
  * equations written as `(if p (= x t) (= x s))` are solved as `(= x (if p t s))`.
  * asserting `p` or `(not p)` where `p` is uninterpreted, causes `p` to be replaced by `true` (or `false`).

* Arithmetic equations
  * It solves `x mod k = s` to `x = k * m' + s`, where m'` is a fresh constant. 
  * It finds variables with unit coefficients in integer linear equations.
  * It solves for `x * Y = Z` under the side-condition `Y != 0` as `x = Z/Y`.
 
It also allows solving for uninterpreted constants that only appear in a single disjuction. For example, 
`(or (= x (+ 5 y)) (= y (+ u z)))` allows solving for `x`. 

### Example

```
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const u Int)
(assert (or (and (= x (+ 5 y)) (> u z)) (= y (+ u z))))
(apply solve-eqs)
```

It produces the goal
```
(goal
  (or (not (<= u z)) (= y (+ u z)))
  :precision precise :depth 1)
```
where `x` was solved as `(+ 5 y)`.

### Notes

* supports unsat cores
* does not support fine-grained proofs

--*/

#pragma once
#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/solve_eqs.h"

inline tactic * mk_solve_eqs_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(euf::solve_eqs, m, s); });
}

/*
  ADD_TACTIC("solve-eqs", "solve for variables.", "mk_solve_eqs_tactic(m, p)")
  ADD_SIMPLIFIER("solve-eqs", "solve for variables.", "alloc(euf::solve_eqs, m, s)")
*/
