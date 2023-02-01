/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_tactic.h

Abstract:

    Tactic for using nonlinear procedure.

Author:

    Leonardo (leonardo) 2012-01-02

Tactic Documentation:

## Tactic nlsat

### Short Description

(try to) solve goal using a nonlinear arithmetic solver

### Example

```z3
(declare-const x Real)
(declare-const y Real)
(assert (> (* x x) (* y x)))
(assert (> x 0))
(assert (< y 1))
(apply (then simplify purify-arith nlsat))
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_nlsat_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC('nlsat', '(try to) solve goal using a nonlinear arithmetic solver.', 'mk_nlsat_tactic(m, p)')
*/

