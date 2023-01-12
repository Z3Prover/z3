/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    lia2pb_tactic.h


Author:

    Leonardo de Moura (leonardo) 2012-02-07.

Tactic Documentation:

## Tactic lia2pb

### Short Description

Reduce bounded LIA benchmark into 0-1 LIA benchmark.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= x 5))
(assert (<= 0 y))
(assert (<= y 5))
(assert (>= (+ (* 2 x) y) 5))
(apply lia2pb)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_lia2pb_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("lia2pb", "convert bounded integer variables into a sequence of 0-1 variables.", "mk_lia2pb_tactic(m, p)")
*/

