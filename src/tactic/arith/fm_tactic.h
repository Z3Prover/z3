/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fm_tactic.h

Author:

    Leonardo de Moura (leonardo) 2012-02-04.

Tactic Documentation:

## Tactic fm

### Short Description

Use Fourier-Motzkin to eliminate variables.
This strategy can handle conditional bounds
(i.e., clauses with at most one constraint).

The tactic occf can be used to put the
formula in OCC form.

### Example

```z3
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const u Real)
(declare-const v Real)
(declare-const w Real)
(declare-fun P (Real) Bool)
(assert (<= x (+ y (* 2.0 z))))
(assert (>= x (- y z)))
(assert (>= x (- y 3 (* 3 z))))
(assert (>= x 5))
(assert (<= x u))
(assert (>= x v))
(assert (P u))
(assert (P v))
(apply fm)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_fm_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("fm", "eliminate variables using fourier-motzkin elimination.", "mk_fm_tactic(m, p)")
*/

