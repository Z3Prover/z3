/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    aig_tactic.h

Abstract:

    Tactic for minimizing circuits using AIGs.

Author:

    Leonardo (leonardo) 2011-10-24

Tactic Documentation:

## Tactic aig

### Short Description

Simplify Boolean structure using AIGs (And-inverter graphs).

### Long Description

And-inverter graphs (AIGs) uses just the Boolean connectives `and` and `not` to encode Boolean
formulas. The circuit representation using AIGs first converts formulas using other connectives to this normal form, 
then performs local simplification steps to minimize the circuit representation.
Note that the simplification steps used by this tactic are heuristic, trading speed for power, 
and do not represent a high-quality circuit minimization approach.

### Example

```z3
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (or (and a b) (and b a c)))
(apply aig)
```

--*/
#pragma once

#include "util/params.h"
class tactic;

tactic * mk_aig_tactic(params_ref const & p = params_ref());
/*
  ADD_TACTIC("aig", "simplify Boolean structure using AIGs.", "mk_aig_tactic()")
*/
