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
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/normalize_bounds.h"
class ast_manager;
class tactic;

tactic * mk_normalize_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

inline tactic* mk_normalize_bounds2_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(normalize_bounds_simplifier, m, p, s);
        });
}

/*
  ADD_TACTIC("normalize-bounds", "replace a variable x with lower bound k <= x with x' = x - k.", "mk_normalize_bounds_tactic(m, p)")
  ADD_TACTIC("normalize-bounds2", "replace a variable x with lower bound k <= x with x' = x - k.", "mk_normalize_bounds2_tactic(m, p)")
  ADD_SIMPLIFIER("normalize-bounds", "replace a variable x with lower bound k <= x with x' = x - k.", "alloc(normalize_bounds_simplifier, m, p, s)")
*/

