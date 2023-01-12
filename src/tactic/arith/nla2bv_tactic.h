/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nla2bv_tactic.cpp

Abstract:


Author:

    Nikolaj (nbjorner) 2011-05-3

Notes:
    Ported to tactic framework on 2012-02-28

Tactic Documentation:

## Tactic nla2bv

### Short Description

Convert quantified NIA problems to bounded bit-vector arithmetic problems.

### Example

```z3
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (* x x y) (*  2 z y y)))
(apply nla2bv)
```

### Notes

* The tactic creates an under-approximation (a stronger set of formulas)


--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_nla2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("nla2bv", "convert a nonlinear arithmetic problem into a bit-vector problem, in most cases the resultant goal is an under approximation and is useul for finding models.", "mk_nla2bv_tactic(m, p)")
*/


