/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv1_blaster_tactic.h

Author:

    Leonardo (leonardo) 2011-10-25

Tactic Documentation:

## Tactic bv1-blast

### Short Description

Reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported).

### Long Description

Rewriter for "blasting" bit-vectors of size n into bit-vectors of size 1.
This rewriter only supports concat and extract operators.
This transformation is useful for handling benchmarks that contain
many BV equalities. 

_Remark_: other operators can be mapped into concat/extract by using
the simplifiers.

### Example

```z3
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 4))
(declare-const z (_ BitVec 4))
(assert (= (concat y z) x))
    (apply bv1-blast)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_bv1_blaster_tactic(ast_manager & m, params_ref const & p = params_ref());
probe * mk_is_qfbv_eq_probe();
/*
  ADD_TACTIC("bv1-blast", "reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported).", "mk_bv1_blaster_tactic(m, p)")
  ADD_PROBE("is-qfbv-eq", "true if the goal is in a fragment of QF_BV which uses only =, extract, concat.", "mk_is_qfbv_eq_probe()")
*/
