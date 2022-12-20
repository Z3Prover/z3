/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_term_ite_tactic.h

Author:

    Leonardo (leonardo) 2011-12-29

Tactic Documentation:

## Tactic elim-term-ite

### Short Description:

Eliminate term if-then-else by adding 
new fresh auxiliary variables.


### Example
 
```z3
(declare-fun f (Int) Int)
(declare-fun p (Int) Bool)
(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)
(declare-const e1 Int) 
(declare-const e2 Int) 
(declare-const e3 Int)
(declare-const e4 Int)
(assert (p (f (if c1 (if c2 e1 (if c3 e2 e3)) e4))))
(apply elim-term-ite) 
```

### Notes

* supports proof terms and unsat cores

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_elim_term_ite_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("elim-term-ite", "eliminate term if-then-else by adding fresh auxiliary declarations.", "mk_elim_term_ite_tactic(m, p)")
*/

