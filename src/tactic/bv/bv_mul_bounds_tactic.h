/*++
Copyright (c) 2026

Module Name:

    bv_mul_bounds_tactic.h

Abstract:

    Tactic wrapper for guarded unsigned multiplication order lemmas.

Tactic Documentation

## Tactic bv-mul-bounds

### Short Description

Add unsigned multiplication order lemmas using existing overflow guards.

### Long Description

For binary products with a common factor c, a <=u b and no unsigned overflow in

    b*c

imply a*c <=u b*c. A strict input order also implies the non-strict product
order, including c=0. The tactic links existing unsigned comparison atoms
and unsigned no-overflow predicates with valid guarded clauses. It does not
infer unconditional bounds from a condition inside another Boolean formula
or introduce multiplication circuits when the needed atoms are absent.
If all complements of an added clause are asserted at the goal's top level,
unit resolution closes the goal while preserving proofs and dependencies.
Flattened products with more than two operands are not matched. This tactic
processes complete goals; it is not registered as an incremental simplifier.

### Example

```z3
(declare-const a (_ BitVec 16))
(declare-const b (_ BitVec 16))
(declare-const c (_ BitVec 16))
(assert (bvult a b))
(assert (bvugt (bvmul a c) (bvmul b c)))
(assert (bvumul_noovfl b c))
(apply (then simplify bv-mul-bounds propagate-values simplify))
```

--*/
#pragma once

#include "ast/simplifiers/bv_mul_bounds.h"
#include "tactic/dependent_expr_state_tactic.h"

inline tactic* mk_bv_mul_bounds_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* { return alloc(bv::mul_bounds, m, s); });
}

Z3_ADD_TACTIC(bv_mul_bounds, "bv-mul-bounds", "add guarded unsigned multiplication order lemmas.", mk_bv_mul_bounds_tactic(m, p));
