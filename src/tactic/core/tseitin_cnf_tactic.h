/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tseitin_cnf_tactic.h

Abstract:


Author:

    Leonardo (leonardo) 2011-12-29

Tactic Documentation:

## Tactic tseitin-cnf

### Short Description

Convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored).

### Long Description

Puts an assertion set in CNF.
Auxiliary variables are used to avoid blowup.

Features:
    
- Efficient encoding is used for commonly used patterns such as:
       `(iff a (iff b c))`
       `(or (not (or a b)) (not (or a c)) (not (or b c)))`

- Efficient encoding is used for chains of if-then-elses 

- Distributivity is applied to non-shared nodes if the blowup is acceptable.
    
- The features above can be disabled/enabled using parameters.

- The assertion-set is only modified if the resultant set of clauses is "acceptable".

Notes: 
    
- Term-if-then-else expressions are not handled by this strategy. 
This kind of expression should be processed by other strategies.

- Quantifiers are treated as "theory" atoms. They are viewed
as propositional variables by this strategy.
    
- The assertion set may contain free variables. 

- This strategy assumes the assertion_set_rewriter was used before invoking it.
In particular, it is more effective when "and" operators
were eliminated.

### Example

```z3
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)

(assert (= a (= b c)))
(apply tseitin-cnf)
```

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_tseitin_cnf_core_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_tseitin_cnf_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("tseitin-cnf", "convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored).", "mk_tseitin_cnf_tactic(m, p)")
  ADD_TACTIC("tseitin-cnf-core", "convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored). This tactic does not apply required simplifications to the input goal like the tseitin-cnf tactic.", "mk_tseitin_cnf_core_tactic(m, p)")
*/

