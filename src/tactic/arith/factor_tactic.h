/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    factor_tactic.h

Abstract:

    Polynomial factorization tactic.

Author:

    Leonardo de Moura (leonardo) 2012-02-03

Tactic Documentation:

## Tactic factor

### Short Description

Factor polynomials in equalities and inequalities.

### Example
```z3
(declare-const x Real)
(declare-const y Real)
(assert (> (* x x) (* x y)))
(apply factor)
```

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/factor_simplifier.h"

inline tactic * mk_factor_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* { return alloc(factor_simplifier, m, p, s); });
}

/*
  ADD_TACTIC("factor", "polynomial factorization.", "mk_factor_tactic(m, p)")
  ADD_SIMPLIFIER("factor", "polynomial factorization.", "mk_factor_simplifier(m, p, s)")
*/
