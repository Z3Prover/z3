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
#ifndef _ADD_BOUNDS_H_
#define _ADD_BOUNDS_H_

#include"params.h"

class ast_manager;
class goal;
class tactic;
class probe;

bool is_unbounded(goal const & g);
probe * mk_is_unbounded_probe();

tactic * mk_add_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
