 /*++
Copyright (c) 2011 Microsoft Corporation
 
Module Name:
 
    bit_blaster_tactic.h
 
Author:
 
   Leonardo (leonardo) 2011-10-25
 
Tactic Documentation:

## Tactic bit-blast

### Short Description

Apply bit-blasting to a given goal.

### Example

```z3
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvule x y))
(apply bit-blast)
```

 --*/

#pragma once
 
#include "util/params.h"
#include "ast/rewriter/bit_blaster/bit_blaster_rewriter.h"
 class ast_manager;
 class tactic;
 
tactic * mk_bit_blaster_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_bit_blaster_tactic(ast_manager & m, bit_blaster_rewriter* rw, params_ref const & p = params_ref());
 /*
  ADD_TACTIC("bit-blast", "reduce bit-vector expressions into SAT.", "mk_bit_blaster_tactic(m, p)")
 */

