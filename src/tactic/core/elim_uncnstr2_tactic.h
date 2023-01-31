/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_unconstr2_tactic.h

Abstract:

    Tactic for eliminating unconstrained terms.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Tactic Documentation:

## Tactic elim-uncnstr

### Short Description

Eliminate Unconstrained uninterpreted constants

### Long Description

The tactic eliminates uninterpreted constants that occur only once in a goal and such that the immediate context
where they occur can be replaced by a fresh constant. We call these occurrences invertible.
It relies on a series of theory specific invertibility transformations.
In the following assume `x` and `x'` occur in a unique subterm and `y` is a fresh uninterpreted constant.

#### Boolean Connectives

| Original Context | New Term | Updated solution        |
|------------------|----------|------------------------ |
`(if c x x')`      | `y`      | `x = x' = y`            |
`(if x x' e)`      |  `y`     | `x = true, x' = y`      |
`(if x t x')`      | `y`      | `x = false, x' = y`     |
`(not x)`          | `y`      | `x = (not y)`           |
`(and x x')`       | `y`      | `x = y, x' = true`      |
`(or  x x')`       | `y`      | `x = y, x' = false`     |
`(= x t)`          | `y`      | `x = (if y t (diff t))` |

where diff is a diagnonalization function available in domains of size `>` 1.

#### Arithmetic

| Original Context | New Term | Updated solution        |
|------------------|----------|------------------------ |
`(+ x t)`          | `y`      | `x = y - t`             |
`(* x x')`         | `y`      | `x = y, x' = 1`         |
`(* -1 x)`         | `y`      | `x = -y`                | 
`(<= x t)`         | `y`      | `x = (if y t (+ t 1))`  |
`(<= t x)`         | `y`      | `x = (if y t (- t 1))`  |

#### Bit-vectors

| Original Context | New Term | Updated solution         |
|------------------|----------|--------------------------|
`(bvadd x t)`      | `y`      | `x = y - t`              |
`(bvmul x x')`     | `y`      | `x = y, x' = 1`          |
`(bvmul odd x)`    | `y`      | `x = inv(odd)*y`         | 
`((extract sz-1 0) x)` | `y`  | `x = y`                  |
`((extract hi lo) x)`  | `y`  | `x = (concat y1 y y2)`   |
`(udiv x x')`      | `y`      | `x = y, x' = 1`          |
`(concat x x')`    | `y`      | `x = (extract hi1 lo1 y)` |
`(bvule x t)`      | `(or y (= t MAX))` | `x = (if y t (bvadd t 1))` |
`(bvule t x)`      | `(or y (= t MIN))` | `x = (if y t (bvsub t 1))` | 
`(bvnot x)`        | `y`                | `x = (bvnot y)`            |
`(bvand x x')`     | `y`                | `x = y, x' = MAX`          |

In addition there are conversions for shift and bit-wise or and signed comparison.

#### Arrays

| Original Context | New Term | Updated solution         |
|------------------|----------|--------------------------|
`(select x t)`     | `y`      | `x = (const y)`          |
`(store x x1 x2)`  | `y`      | `x2 = (select x x1), x = y, x1 = arb` | 

#### Algebraic Datatypes

| Original Context | New Term | Updated solution         |
|------------------|----------|--------------------------|
`(head x)`         | `y`      | `x = (cons y arb)`       |



### Example

```z3
(declare-const x Int)
(declare-const y Int)
(declare-fun p (Int) Bool)    
(assert (>= (+ y (+ x y)) y))
(assert (p y))
(apply elim-uncnstr)
(assert (p (+ x y)))
(apply elim-uncnstr)
```

### Notes

* supports unsat cores
* does not support fine-grained proofs

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/elim_unconstrained.h"

inline tactic * mk_elim_uncnstr2_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(elim_unconstrained, m, s); });
}

/*
  ADD_TACTIC("elim-uncnstr2", "eliminate unconstrained variables.", "mk_elim_uncnstr2_tactic(m, p)")
  ADD_SIMPLIFIER("elim-unconstrained", "eliminate unconstrained variables.", "alloc(elim_unconstrained, m, s)")
*/
