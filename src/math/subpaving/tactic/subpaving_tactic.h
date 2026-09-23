/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_tactic.h

Abstract:

    "Fake" tactic used to test subpaving module.

Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

## Tactic subpaving

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_subpaving_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(subpaving, "subpaving", "tactic for testing subpaving module.", mk_subpaving_tactic(m, p));

