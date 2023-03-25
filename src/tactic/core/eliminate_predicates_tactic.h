/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    eliminate_predicates_tactic.h

Abstract:

    Tactic for eliminating macros and predicates

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Tactic Documentation:

## Tactic elim-predicates

### Short Description
Eliminates predicates and macros from a formula.

### Long Description
The tactic subsumes the functionality of `macro-finder` and `quasi-macros`.
Besides finding macros, it eliminates predicates using Davis-Putnam
resolution.

### Example

the predicate `p` occurs once positively. All negative occurrences of `p` are resolved against this positive occurrence.
The result of resolution is a set of equalities between arguments to `p`. The function `f` is replaced by a partial solution.

```z3
(declare-fun f (Int Int Int) Int)
(declare-fun p (Int) Bool)
(declare-const a Int)
(declare-const b Int)

(assert (forall ((x Int) (y Int)) (= (f x y (+ x y)) (* 2 x y))))
(assert (p (f 8 a (+ a 8))))
(assert (not (p (f 0 a (+ a 8)))))
(assert (not (p (f 2 a (+ a 8)))))
(assert (not (p (f 1 a (+ a b)))))
(apply elim-predicates)
```

### Notes

* support unsat cores
* does not support proofs

--*/
#pragma once

#include "util/params.h"
#include "ast/simplifiers/eliminate_predicates.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"

inline tactic * mk_eliminate_predicates_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(eliminate_predicates, m, s); });
}

/*
  ADD_TACTIC("elim-predicates", "eliminate predicates, macros and implicit definitions.", "mk_eliminate_predicates_tactic(m, p)")
  ADD_SIMPLIFIER("elim-predicates", "eliminate predicates, macros and implicit definitions.", "alloc(eliminate_predicates, m, s)")
*/
