/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion_tactic.h

Abstract:

    Tactic for simplifying with equations.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_euf_completion_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("euf-completion", "simplify using equalities.", "mk_euf_completion_tactic(m, p)")
*/


