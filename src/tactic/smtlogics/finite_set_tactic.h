/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    finite_set_tactic.h

Abstract:

    Preprocessing and solving tactics for the native FiniteSet theory.

Tactic Documentation:

## Tactic finite-set

Simplify bounded quantification encoded by finite-set filters, then invoke
the SMT solver. The finite-set-simplify tactic exposes preprocessing alone.
Both preserve models and unsat cores. Proof-enabled goals skip the finite-set
rewrites, which do not currently produce proofs.

### Example

```z3
(declare-const S (FiniteSet Int))
(assert (not (= (set.filter (lambda ((x Int)) (= x 5)) S)
                (as set.empty (FiniteSet Int)))))
(check-sat-using finite-set)
(get-model)
```

--*/
#pragma once

#include "tactic/tactic.h"

tactic* mk_finite_set_simplify_tactic(ast_manager& m, params_ref const& p = params_ref());
tactic* mk_finite_set_tactic(ast_manager& m, params_ref const& p = params_ref());

Z3_ADD_TACTIC(finite_set_simplify, "finite-set-simplify", "simplify bounded quantification over native finite sets.", mk_finite_set_simplify_tactic(m, p));
Z3_ADD_TACTIC(finite_set, "finite-set", "preprocess native finite-set constraints and solve using SMT.", mk_finite_set_tactic(m, p));
