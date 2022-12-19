/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    dt2bv_tactic.h

Author:

    nbjorner 2016-07-22

Tactic Documentation

## Tactic dt2bv

### Short Description

Tactic that eliminates finite domain data-types.

### Example

```z3
(declare-datatypes ((Color 0)) (((Red) (Blue) (Green) (DarkBlue) (MetallicBlack) (MetallicSilver) (Silver) (Black))))
(declare-const x Color)
(declare-const y Color)
(assert (not (= x y)))
(assert (not (= x Red)))
(apply dt2bv)
```

--*/
#pragma once

#include "util/params.h"
#include "util/obj_hashtable.h"
class ast_manager;
class tactic;

tactic * mk_dt2bv_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("dt2bv", "eliminate finite domain data-types. Replace by bit-vectors.", "mk_dt2bv_tactic(m, p)")
*/

