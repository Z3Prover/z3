/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    add_bounds.h

Abstract:

    

Author:

    Leonardo de Moura (leonardo) 2011-06-30.

Tactic Documentation:

## Tactic add-bounds

### Short Description

Tactic for bounding unbounded variables.

### Long Description

The tactic creates a stronger sub-goal by adding bounds to variables.
The new goal may not be satisfiable even if the original goal is.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(assert (> (+ x y) 10))
(apply add-bounds)
```

--*/
#pragma once

#include "util/params.h"
#include "tactic/probe.h"
#include "tactic/tactic.h"

class ast_manager;
class goal;
class tactic;
class probe;

bool is_unbounded(goal const & g);
probe * mk_is_unbounded_probe();

tactic * mk_add_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(add_bounds, "add-bounds", "add bounds to unbounded variables (under approximation).", mk_add_bounds_tactic(m, p));
Z3_ADD_PROBE(is_unbounded, "is-unbounded", "true if the goal contains integer/real constants that do not have lower/upper bounds.", mk_is_unbounded_probe());

