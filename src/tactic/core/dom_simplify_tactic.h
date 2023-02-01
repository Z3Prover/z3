/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dom_simplify_tactic.cpp


Abstract:

    Dominator-based context simplifer.

Author:

    Nikolaj and Nuno 

Tactic Documentation:

## Tactic dom-simplify

### Short Description

Apply dominator simplification rules

### Long Description

Dominator-based simplification is a context dependent simplification function that uses a dominator tree to control the number of paths it 
visits during simplification. The expression DAG may have an exponential number of paths, but only paths corresponding to a dominator
tree are visited. Since the paths selected by the dominator trees are limited, the simplifier may easily fail to simplify within a context. 

### Example

```z3
(declare-const a Bool)
(declare-const b Bool)
(assert (and a (or a b)))
(apply dom-simplify)
```


--*/

#pragma once

#include "ast/ast.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/dom_simplifier.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/dominator_simplifier.h"

inline tactic* mk_dom_simplify_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p,
        [](auto& m, auto& p, auto& s) -> dependent_expr_simplifier* { return alloc(dominator_simplifier, m, s, mk_expr_substitution_simplifier(m), p); });
}

/*
ADD_TACTIC("dom-simplify", "apply dominator simplification rules.", "mk_dom_simplify_tactic(m, p)")
ADD_SIMPLIFIER("dom-simplify", "apply dominator simplification rules.", "alloc(dominator_simplifier, m, s, mk_expr_substitution_simplifier(m), p)")
*/

