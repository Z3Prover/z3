/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    fix_dl_var_tactic.h

Abstract:



Author:

    Leonardo (leonardo) 2011-12-29

Tactic Documentation:

## Tactic fix-dl-var

### Short Description

Fix a difference logic variable to `0`.
If the problem is in the difference logic fragment, that is, all arithmetic terms
are of the form `(x + k)`, and the arithmetic atoms are of the
form `x - y <= k` or `x - y = k`. Then, we can set one variable to `0`.

This is useful because, many bounds can be exposed after this operation is performed.

### Example

```z3
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (<= (+ x (* -1.0 y)) 3.0))
(assert (<= (+ x (* -1.0 z)) 5.0))
(apply fix-dl-var)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_fix_dl_var_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("fix-dl-var", "if goal is in the difference logic fragment, then fix the variable with the most number of occurrences at 0.", "mk_fix_dl_var_tactic(m, p)")
*/

