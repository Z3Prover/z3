/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    card2bv_tactic.h

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-20

Tactic Documentation:

## Tactic card2bv

### Short Description

Tactic for converting Pseudo-Boolean constraints to bit-vectors.

### Long Description 

The tactic implements a set of standard methods for converting cardinality and Pseudo-Boolean constraints into bit-vector or propositional formulas
(using basic logical connectives, conjunction, disjunction, negation). The conversions from cardinality constraints are controlled
separately from the conversions from Pseudo-Boolean constraints using different parameters.

### Example

```z3
(declare-const a1 Bool)
(declare-const a2 Bool)
(declare-const a3 Bool)
(declare-const a4 Bool)
(declare-const a5 Bool)
(declare-const a6 Bool)
(push)
(assert ((_ at-most 1) a1 a2 a3 a4 a5 a6))
(assert ((_ at-most 2) a1 a2 a3 a4 a5 a6))
(apply (with card2bv :cardinality.encoding unate))
(apply (with card2bv :cardinality.encoding circuit))
(apply (with card2bv :cardinality.encoding ordered))
(apply (with card2bv :cardinality.encoding grouped))
(apply (with card2bv :cardinality.encoding bimander))
(pop)
(assert ((_ pbge 5 2 3 4 4 3 5) a1 a2 a3 a4 a5 a6))
(apply (with card2bv :pb.solver totalizer))
(apply (with card2bv :pb.solver sorting))
(apply (with card2bv :pb.solver binary_merge))
(apply (with card2bv :pb.solver bv))
(apply (with card2bv :pb.solver solver))
```

### Notes

* supports cores
* does not support proofs

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/card2bv.h"

inline tactic* mk_card2bv_tactic(ast_manager& m, params_ref const& p = params_ref()) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return alloc(card2bv, m, p, s); });
}

/*
  ADD_TACTIC("card2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_card2bv_tactic(m, p)")
  ADD_SIMPLIFIER("card2bv", "convert pseudo-boolean constraints to bit-vectors.", "alloc(card2bv, m, p, s)")
*/
