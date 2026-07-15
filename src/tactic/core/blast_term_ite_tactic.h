/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    blast_term_ite_tactic.h
   

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-4

Tactic Documentation:

## Tactic blast-term-ite

### Short Description:

Blast term if-then-else by hoisting them up.
This is expensive but useful in some cases, such as
for enforcing constraints being in difference logic.
Use `elim-term-ite` elsewhere when possible.

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
(apply blast-term-ite) 
```

### Notes



--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/blast_term_ite_simplifier.h"

inline tactic * mk_blast_term_ite_tactic(ast_manager & m, params_ref const & p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* {
            return alloc(blast_term_ite_simplifier, m, p, s);
        });
}

/*
    ADD_TACTIC("blast-term-ite", "blast term if-then-else by hoisting them.", "mk_blast_term_ite_tactic(m, p)")
    ADD_SIMPLIFIER("blast-term-ite", "blast term if-then-else by hoisting them.", "alloc(blast_term_ite_simplifier, m, p, s)")
*/

void blast_term_ite(expr_ref& fml, unsigned max_inflation);

