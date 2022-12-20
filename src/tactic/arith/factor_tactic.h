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
class ast_manager;
class tactic;

tactic * mk_factor_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("factor", "polynomial factorization.", "mk_factor_tactic(m, p)")
*/
