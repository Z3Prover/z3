/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv_bounds_tactic.h

Author:

    Nuno Lopes (nlopes) 2016-2-12
    Nikolaj Bjorner (nbjorner)

Tactic Documentation:

## Tactic propagate-bv-bounds

### Short Description

Contextual bounds simplification tactic.

### Example

```z3
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (bvule (_ bv4 32) x))
(assert (bvule x (_ bv24 32)))
(assert (or (bvule x (_ bv100 32)) (bvule (_ bv32 32) x)))
(apply propagate-bv-bounds)
```

### Notes

* assumes that bit-vector inequalities have been simplified to use bvule/bvsle

--*/
#pragma once
#include "tactic/tactic.h"
#include "ast/simplifiers/bv_bounds_simplifier.h"

tactic * mk_bv_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_dom_bv_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("propagate-bv-bounds", "propagate bit-vector bounds by simplifying implied or contradictory bounds.", "mk_bv_bounds_tactic(m, p)")

  ADD_SIMPLIFIER("propagate-bv-bounds", "propagate bit-vector bounds by simplifying implied or contradictory bounds.", "mk_bv_bounds_simplifier(m, p, s)")

  ADD_TACTIC("propagate-bv-bounds2", "propagate bit-vector bounds by simplifying implied or contradictory bounds.", "mk_dom_bv_bounds_tactic(m, p)")


*/

