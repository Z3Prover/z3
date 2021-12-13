/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-12

Notes:

This is a place holder for simplification.

- Replace literals of the form p < 1 (which is ~(p >= 1)) by p <= 0

- Rewrite clauses using factoring and normalization rules

  - p*q <= 0 or C
    -> p <= 0 or C, q <= 0 or C

  - ovfl(1, x) or C 
    -> C

- Drop redundant literals from lemmas.

- Generalize lemmas by replacing equalities or destructive resolution.

  - x = k => C[x]
    - C[k]

  - x = k & y = k' => ax + by <= c
    - lo <= x <= k & lo' <= y <= k' => ax + by <= c

  
--*/
#include "math/polysat/solver.h"
#include "math/polysat/simplify.h"

namespace polysat {

    simplify::simplify(solver& s):
        s(s)
    {}

    bool simplify::should_apply() const { 
        return false; 
    }

    void simplify::operator()() {}

}
