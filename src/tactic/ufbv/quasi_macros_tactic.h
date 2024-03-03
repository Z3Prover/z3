/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    quasi_macros_tactic.h

Abstract:

    Quasi-Macros

Author:

    Christoph (cwinter) 2012-10-26

Tactic Documentation

## Tactic quasi-macro-finder

### Short Description
Identifies and applies quasi-macros.

### Long Description

A quasi macro defines a function symbol that contains more arguments than the number of bound variables it defines.
The additional arguments are functions of the bound variables.
 
### Example

```z3
(declare-fun f (Int Int Int) Int)
(declare-fun p (Int) Bool)
(declare-const a Int)

(assert (forall ((x Int) (y Int)) (= (f x y 1) (* 2 x y))))
(assert (p (f 8 a (+ a 8))))
(apply quasi-macros)
```

### Notes

* Supports proofs and cores


--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_quasi_macros_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("quasi-macros",  "Identifies and applies quasi-macros.", "mk_quasi_macros_tactic(m, p)")
*/

