/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv_slice_tactic.h

Abstract:

    Tactic for simplifying with bit-vector slices

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Tactic Documentation

## Tactic bv-slice

### Short Description

Slices bit-vectors into sub-ranges to allow simplifying sub-ranges.

### Long Description

It rewrites a state using bit-vector slices. 
Slices are extracted from bit-vector equality assertions.
An equality assertion may equate a sub-range of a bit-vector
with a constant. The tactic ensures that all occurrences of the
subrange are replaced by the constants to allow additional 
simplification

### Example

```z3 ignore-errors
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
        (assert (= ((_ extract 31 16) x) (_ bv123 16)))
(assert (= ((_ extract 15 0) x) ((_ extract 16 1) y)))
(assert (= (bvadd x x) y))
(apply bv-slice)
```

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/bv_slice.h"

class ast_manager;
class tactic;

inline tactic* mk_bv_slice_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(bv::slice, m, s); });
}


/*
  ADD_TACTIC("bv-slice", "simplify using bit-vector slices.", "mk_bv_slice_tactic(m, p)")
  ADD_SIMPLIFIER("bv-slice", "simplify using bit-vector slices.", "alloc(bv::slice, m, s)")
*/


