/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    bvarray2uf_tactic.h

Author:

    Christoph (cwinter) 2015-11-04

Tactic Documentation:

## Tactic bvarray2uf

### Short Description

Tactic that rewrites bit-vector arrays into bit-vector
(uninterpreted) functions.

### Example

```z3
(declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(assert (= (select a b) c))
(apply bvarray2uf)
```

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "tactic/bv/bvarray2uf_simplifier.h"

class ast_manager;
class tactic;

inline tactic * mk_bvarray2uf_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(bvarray2uf_simplifier, m, p, s);
        });
}

/*
    ADD_TACTIC("bvarray2uf", "Rewrite bit-vector arrays into bit-vector (uninterpreted) functions.", "mk_bvarray2uf_tactic(m, p)")
    ADD_SIMPLIFIER("bvarray2uf", "Rewrite bit-vector arrays into bit-vector (uninterpreted) functions.", "alloc(bvarray2uf_simplifier, m, p, s)")
*/


