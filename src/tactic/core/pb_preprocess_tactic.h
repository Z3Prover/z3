/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_preprocess_tactic.h

Abstract:

    Pre-process pseudo-Boolean inequalities using 
    generalized Davis Putnam (resolution) to eliminate variables.

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-23

Documentation:

## Tactic pb-preprocess

### Short Description:

The tactic eliminates variables from pseudo-Boolean inequalities and performs algebraic simplifcations on formulas

### Long Description

Resolution for PB constraints require the implicit 
inequalities that each variable ranges over [0,1]
so not all resolvents produce smaller sets of clauses.

We here implement subsumption resolution.  

```
    x + y >= 1
    A~x + B~y + Cz >= k
    ---------------------
    Cz >= k - B    
```

where `A <= B` and `x, y` do not occur elsewhere.    


### Example
 
```z3
  (declare-const x Bool)
  (declare-const y Bool)
  (declare-const z Bool)
  (declare-const u Bool)
  (declare-const v Bool)
  (assert ((_ pbge 1 1 1 2) (not x) (not y) (not z)))
  (assert ((_ pbge 1 1 1 2) x u v))
  (assert (not (and y v)))
  (assert (not (and z u)))
  (apply pb-preprocess)
```

### Notes

* supports unsat cores
* does not support proof terms

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_pb_preprocess_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("pb-preprocess", "pre-process pseudo-Boolean constraints a la Davis Putnam.", "mk_pb_preprocess_tactic(m, p)")
*/


