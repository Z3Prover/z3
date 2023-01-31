/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    distribute_forall_tactic.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-02-18.

Tactic Documentation:

## Tactic distribute-forall

### Short Description:

Distribute $\forall$ over conjunctions (and distribute $\exists$ over disjunctions)

### Example
 
```z3
  (declare-const x Int)
  (declare-fun p (Int) Bool)
  (declare-fun q (Int) Bool)
  (assert (forall ((x Int)) (and (p x) (q x))))
  (apply distribute-forall)
```

### Notes

* supports unsat cores, proof terms


--*/
#pragma once

#include "util/params.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/distribute_forall.h"

inline tactic * mk_distribute_forall_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(distribute_forall_simplifier, m, p, s); });
}

/*
  ADD_TACTIC("distribute-forall", "distribute forall over conjunctions.", "mk_distribute_forall_tactic(m, p)")
  ADD_SIMPLIFIER("distribute-forall", "distribute forall over conjunctions.", "alloc(distribute_forall_simplifier, m, p, s)")
*/

