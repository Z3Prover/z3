/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    bv_divrem_bounds_tactic.h

Abstract:

    Tactic wrapper around the bv::divrem_bounds simplifier. It adds range
    lemmas for bit-vector division and remainder terms with a non-constant
    divisor. See ast/simplifiers/bv_divrem_bounds.h for details.

Author:

    Nikolaj Bjorner (nbjorner)

Tactic Documentation

## Tactic bv-divrem-bounds

### Short Description

Add range lemmas for bit-vector division/remainder terms with a symbolic divisor.

### Long Description

For a divisor `b` that is not a numeral, the remainder magnitude is bounded by
the divisor magnitude and the unsigned quotient is bounded by the dividend.
These facts are hidden once a division circuit is bit-blasted, so the tactic
emits them as implied lemmas up front, letting a downstream SAT solver reason
about magnitudes without unfolding the circuit.

### Example

```z3
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (= (bvsrem a (bvadd b c)) #x05))
(apply bv-divrem-bounds)
```

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/bv_divrem_bounds.h"

class ast_manager;
class tactic;

inline tactic* mk_bv_divrem_bounds_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* { return alloc(bv::divrem_bounds, m, s); });
}

/*
  ADD_TACTIC("bv-divrem-bounds", "add range lemmas for bit-vector division/remainder terms with a symbolic divisor.", "mk_bv_divrem_bounds_tactic(m, p)")
  ADD_SIMPLIFIER("bv-divrem-bounds", "add range lemmas for bit-vector division/remainder terms with a symbolic divisor.", "alloc(bv::divrem_bounds, m, s)")
*/
