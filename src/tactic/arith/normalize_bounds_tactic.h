/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    normalize_bounds_tactic.h

Author:

    Leonardo de Moura (leonardo) 2011-10-21.

Tactic Documentation:

## Tactic normalize-bounds

### Short Description

Replace $x$ with $x' + l$, when $l \leq x$
where $x'$ is a fresh variable.
Note that, after the transformation $0 \leq x'$.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (<= 3 x))
(assert (<= (+ x y) z))
(apply normalize-bounds)
```

### Notes

* supports proofs and cores

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_normalize_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(normalize_bounds, "normalize-bounds", "replace a variable x with lower bound k <= x with x' = x - k.", mk_normalize_bounds_tactic(m, p));

