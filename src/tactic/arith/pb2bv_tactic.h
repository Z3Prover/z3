/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pb2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Christoph (cwinter) 2012-02-15

Tactic Documentation:

## Tactic pb2bv

### Short Description

Convert pseudo-boolean constraints to bit-vectors

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const u Int)
(assert (<= 0 x))
(assert (<= 0 y))
(assert (<= 0 z))
(assert (<= 0 u))
(assert (<= x 1))
(assert (<= y 1))
(assert (<= z 1))
(assert (<= u 1))
(assert (>= (+ (* 3 x) (* 2 y) (* 2 z) (* 2 u)) 4))
(apply pb2bv)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_pb2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("pb2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_pb2bv_tactic(m, p)")
*/

probe * mk_is_pb_probe();

/*
  ADD_PROBE("is-pb", "true if the goal is a pseudo-boolean problem.", "mk_is_pb_probe()")
*/

