/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bv_size_reduction.h

Abstract:


Author:

    Leonardo (leonardo) 2012-02-19

Notes:

Tactic Documentation:

## Tactic reduce-bv-size

### Short Description

Rry to reduce bit-vector sizes using inequalities.

### Long Description

Reduce the number of bits used to encode constants, by using signed bounds.
Example: suppose $x$ is a bit-vector of size 8, and we have
signed bounds for $x$ such that:

```
        -2 <= x <= 2
```

Then, $x$ can be replaced by  `((sign-extend 5) k)`
where `k` is a fresh bit-vector constant of size 3.

### Example

```z3
(declare-const x (_ BitVec 32))
(assert (bvsle (bvneg (_ bv2 32)) x))
(assert (bvsle x (_ bv2 32)))
(assert (= (bvmul x x) (_ bv9 32)))
(apply (and-then simplify reduce-bv-size))
```

### Notes

* does not support proofs, nor unsat cores

--*/
#pragma once

#include "util/params.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/bv_size_reduction.h"
class ast_manager;
class tactic;

inline tactic * mk_bv_size_reduction_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
                     return alloc(bv_size_reduction_simplifier, m, p, s);
                 });
}
/*
  ADD_TACTIC("reduce-bv-size", "try to reduce bit-vector sizes using inequalities.", "mk_bv_size_reduction_tactic(m, p)")
  ADD_SIMPLIFIER("reduce-bv-size", "try to reduce bit-vector sizes using inequalities.", "alloc(bv_size_reduction_simplifier, m, p, s)")
*/
