/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion_tactic.h

Abstract:

    Tactic for simplifying with equations.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Tactic Documentation:

## Tactic euf-completion

### Short Description

Uses the ground equalities as a rewrite system. The formulas are simplified
using the rewrite system. 

### Long Description

The tactic uses congruence closure to represent and orient the rewrite system. Equalities from the formula
are inserted in the an E-graph (congruence closure structure) and then a representative that is most shallow
is extracted.


--*/
#pragma once

#include "util/params.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "ast/simplifiers/euf_completion.h"

class ast_manager;
class tactic;

tactic * mk_euf_completion_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("euf-completion", "simplify using equalities.", "mk_euf_completion_tactic(m, p)")
  ADD_SIMPLIFIER("euf-completion", "simplify modulo congruence closure.", "alloc(euf::completion, m, s)")
*/


