/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    symmetry_reduce.h

Abstract:

    Add symmetry breaking predicates to assertion sets.

Author:

    Nikolaj (nbjorner) 2011-05-31


Tactic Documentation:

## Tactic symmetry-reduce

### Short Description

Apply symmetry reduction

### Long Description

The tactic applies symmetry reduction for uninterpreted functions and equalities.
It applies a straight-forward adaption of an algorithm proposed for veriT.


--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_symmetry_reduce_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("symmetry-reduce", "apply symmetry reduction.", "mk_symmetry_reduce_tactic(m, p)")
*/

