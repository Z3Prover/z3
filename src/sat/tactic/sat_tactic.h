/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_tactic.cpp

Abstract:

    Tactic for using the SAT solver and its preprocessing capabilities.
    
Author:

    Leonardo (leonardo) 2011-10-26

Tactic Documentation:

## Tactic sat

### Short Description

Try to solve goal using a SAT solver

## Tactic sat-preprocess

### Short Description 

Apply SAT solver preprocessing procedures (bounded resolution, Boolean constant propagation, 2-SAT, subsumption, subsumption resolution).

### Example

```z3
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)
(declare-fun p (Bool) Bool)
(assert (=> a b))
(assert (=> b c))
(assert a)
(assert (not c))
(apply sat-preprocess)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_sat_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_sat_preprocessor_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC('sat', '(try to) solve goal using a SAT solver.', 'mk_sat_tactic(m, p)')
  ADD_TACTIC('sat-preprocess', 'Apply SAT solver preprocessing procedures (bounded resolution, Boolean constant propagation, 2-SAT, subsumption, subsumption resolution).', 'mk_sat_preprocessor_tactic(m, p)')
*/

