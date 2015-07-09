/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    add_bounds.h

Abstract:

    Tactic for bounding unbounded variables.

Author:

    Leonardo de Moura (leonardo) 2011-06-30.

Revision History:

--*/
#ifndef ADD_BOUNDS_H_
#define ADD_BOUNDS_H_

#include"params.h"

class ast_manager;
class goal;
class tactic;
class probe;

bool is_unbounded(goal const & g);
probe * mk_is_unbounded_probe();

tactic * mk_add_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("add-bounds", "add bounds to unbounded variables (under approximation).", "mk_add_bounds_tactic(m, p)")
  ADD_PROBE("is-unbounded", "true if the goal contains integer/real constants that do not have lower/upper bounds.", "mk_is_unbounded_probe()")
*/

#endif
