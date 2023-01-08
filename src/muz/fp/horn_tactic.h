/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    horn_tactic.h

Abstract:

    PDR as a tactic to solve Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-16.

Tactic Documentation:

## Tactic horn

### Short Description

Solve a set of Horn clauses using the SPACER engine.

### Long Description

The SPACER engine is specialized to solving Constrained Horn Clauses.
This tactic instructs 

## Tactic horn-simplify

### Short Description

Apply pre-processing simplification rules to a set of Horn clauses

### Long Description
This tactic exposes pre-processing simplification rules for Constrained Horn Clauses.
They include a repertoire of simplification options that can be controlled by toggling
the `fp` parameters.

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_horn_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("horn", "apply tactic for horn clauses.", "mk_horn_tactic(m, p)")
*/

tactic * mk_horn_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("horn-simplify", "simplify horn clauses.", "mk_horn_simplify_tactic(m, p)")
*/
