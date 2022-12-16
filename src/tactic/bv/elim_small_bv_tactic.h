/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    elim_small_bv.h

Abstract:

    Tactic that eliminates small, quantified bit-vectors.

Author:

    Christoph (cwinter) 2015-11-09

Revision History:

Tactic Documentation

## Tactic elim-small-bv

### Short Description

Eliminate small, quantified bit-vectors by expansion

### Example

```z3
(declare-fun p ((_ BitVec 2)) Bool)
(assert (forall ((x (_ BitVec 2))) (p x)))
(apply elim-small-bv)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_elim_small_bv_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("elim-small-bv", "eliminate small, quantified bit-vectors by expansion.", "mk_elim_small_bv_tactic(m, p)")
*/
