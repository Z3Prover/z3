/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    demodulator_tactic.h

Abstract:

    Tactic for rewriting goals using quantified equalities

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Tactic Documentation:

## Tactic demodulator

### Short Description:

Extracts equalities from quantifiers and applies them for simplification

### Long Description

In first-order theorem proving (FOTP), a demodulator is a universally quantified formula of the form:

`Forall X1, ..., Xn.  L[X1, ..., Xn] = R[X1, ..., Xn]`
Where `L[X1, ..., Xn]` contains all variables in `R[X1, ..., Xn]`, and 
`L[X1, ..., Xn]` is "bigger" than `R[X1, ...,Xn]`.

The idea is to replace something big `L[X1, ..., Xn]` with something smaller `R[X1, ..., Xn]`.

After selecting the demodulators, we traverse the rest of the formula looking for instances of `L[X1, ..., Xn]`.
Whenever we find an instance, we replace it with the associated instance of `R[X1, ..., Xn]`.

For example, suppose we have

```
Forall x, y.  f(x+y, y) = y
and
f(g(b) + h(c), h(c)) <= 0
```

The term `f(g(b) + h(c), h(c))` is an instance of `f(x+y, y)` if we replace `x <- g(b)` and `y <- h(c)`.
So, we can replace it with `y` which is bound to `h(c)` in this example. So, the result of the transformation is:

```
Forall x, y.  f(x+y, y) = y
and
h(c) <= 0
```

### Example
 
```
  (declare-sort S 0)
  (declare-sort S1 0)
  (declare-sort S2 0)
  (declare-fun f () S)
  (declare-fun f1 () S)
  (declare-fun f2 (S1 S) S)
  (declare-fun f3 (S2 S) S1)
  (declare-fun f4 () S)
  (declare-fun f5 () S2)
  (assert (not (= f1 (f2 (f3 f5 f4) f))))
  (assert (forall ((q S) (v S)) (or (= q v) (= f1 (f2 (f3 f5 q) v)) (= (f2 (f3 f5 v) q) f1))))
  (assert (forall ((q S) (x S)) (not (= (f2 (f3 f5 q) x) f1))))
  (apply demodulator)
```

It generates

```
  (goals
  (goal
    (forall ((q S) (v S)) (= q v))
    (forall ((q S) (x S)) (not (= (f2 (f3 f5 q) x) f1)))
    :precision precise :depth 1)
  )
```

### Notes

* supports unsat cores
* does not support fine-grained proofs

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/demodulator_simplifier.h"

inline tactic * mk_demodulator_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(demodulator_simplifier, m, p, s); });
}

/*
  ADD_TACTIC("demodulator", "extracts equalities from quantifiers and applies them to simplify.", "mk_demodulator_tactic(m, p)")
  ADD_SIMPLIFIER("demodulator", "extracts equalities from quantifiers and applies them to simplify.", "alloc(demodulator_simplifier, m, p, s)")
*/
