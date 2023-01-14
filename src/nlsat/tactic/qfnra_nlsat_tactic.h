/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_nlsat_tactic.h

Abstract:

    Tactic based on nlsat for solving QF_NRA problems

Author:

    Leonardo (leonardo) 2012-01-23

Tactic Documentation:

## Tactic qfnra-nlsat

### Short Description

Self-contained tactic that attempts to solve goal using a nonlinear arithmetic solver.
It first applies tactics, such as `purify-arith` to convert the goal into a format
where the `nlsat` tactic applies.

### Example

```z3
(declare-const x Real)
(declare-const y Real)
(assert (> (* x x) (* y x)))
(assert (> x 0))
(assert (< y 1))
(apply qfnra-nlsat)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfnra_nlsat_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("qfnra-nlsat", "builtin strategy for solving QF_NRA problems using only nlsat.", "mk_qfnra_nlsat_tactic(m, p)")
*/

