/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_tactic.h

Abstract:

    DER tactic

Author:

    Leonardo de Moura (leonardo) 2012-10-20

Tactic Documentation:

## Tactic der

### Short Description:

The tactic performs _destructive equality resolution_.

### Long Description

Destructive equality resolution replaces bound variables that are
_solved_ by their solutions in formulas. In short, the destructive
equality resolution rule takes the form:

```
   (forall (X Y) (or X /= s C[X])) --> (forall (Y) C[Y])
```


### Example
 
```z3
  (declare-fun f (Int) Int)
  (declare-fun p (Int Int) Bool)
  (assert (forall ((x Int) (y Int)) (or (not (= x (f y))) (p x y))))
  (apply der)
```

### Notes

* supports unsat cores, proof terms


--*/
#pragma once

class ast_manager;
class tactic;

tactic * mk_der_tactic(ast_manager & m);

/*
  ADD_TACTIC("der", "destructive equality resolution.", "mk_der_tactic(m)")
*/

