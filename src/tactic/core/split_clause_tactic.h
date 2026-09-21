/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    split_clause_tactic.h

Author:

    Leonardo (leonardo) 2011-11-21

Tactic Documentation:

## Tactic split-clause

### Short Description

Tactic that creates a subgoal for each literal in a clause `(l_1 or ... or l_n)`.
The tactic fails if the main goal does not contain any clause.

### Example

```z3
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(apply split-clause)
```


--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class tactic;

tactic * mk_split_clause_tactic(params_ref const & p = params_ref());

Z3_ADD_TACTIC(split_clause, "split-clause", "split a clause in many subgoals.", mk_split_clause_tactic(p));

