/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    propagate_values2_tactic.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

Tactic Documentation:

## Tactic propagate-values

### Short Description:

Tactic for propagating equalities `(= t v)` where `v` is a value

### Long Description

In a context where terms are equated to constants it is invariably beneficial to 
replace terms, that can be compound, with the constants and then simplify the resulting formulas.
The propagate-values tactic accomplishes the task of replacing such terms.

### Example
 
```z3
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= 1 (f (+ x y))))
(assert (= 2 x))
(assert (> (f (+ 2 y)) y))
(apply propagate-values)
```

### Notes

* supports unsat cores


--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/propagate_values.h"

inline tactic * mk_propagate_values2_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(propagate_values, m, p, s); });
}

/*
  ADD_TACTIC("propagate-values2", "propagate constants.", "mk_propagate_values2_tactic(m, p)")
  ADD_SIMPLIFIER("propagate-values", "propagate constants.", "alloc(propagate_values, m, p, s)")
*/
