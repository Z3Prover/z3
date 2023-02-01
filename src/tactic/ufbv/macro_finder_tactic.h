/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    macro_finder_tactic.h

Abstract:

    Macro finder

Author:

    Christoph (cwinter) 2012-10-26

Tactic Documentation

## Tactic macro-finder

### Short Description 

Identifies and applies macros.

### Long Description

It finds implicit macro definitions in quantifiers. 
A main instance of a macro an equality that defines a function `f` using some term `t` that does not contain `f`.
Other instances of macros are also recognized by the macro finder.

* `(forall (x) (= (f x) t))`

* `not (= (p x) t)` is recognized as `(p x) = (not t)`

* `(iff (= (f x) t) cond)`  rewrites to `(f x) = (if cond t else (k x))`
   * add clause `(not (= (k x) t))`

* `(= (+ (f x) s) t)` becomes `(= (f x) (- t s))`

* `(= (+ (* -1 (f x)) x) t)`  becomes `(= (f x) (- (- t s)))`

### Example

```z3
(declare-fun f (Int) Int)
(declare-fun p (Int) Bool)

(assert (forall ((x Int)) (= (+ (f x) x) 3)))
(assert (p (f 8)))
(apply macro-finder)
```

### Notes

* Supports proofs, unsat cores, but not goals with recursive function definitions.

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_macro_finder_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("macro-finder",  "Identifies and applies macros.", "mk_macro_finder_tactic(m, p)")
*/

