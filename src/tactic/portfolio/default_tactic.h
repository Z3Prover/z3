/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    default_tactic.h

Abstract:

    General purpose tactic for the Z3 logic (when the logic is not specified).

Author:

    Leonardo (leonardo) 2012-02-22

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_default_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(default, "default", "default strategy used when no logic is specified.", mk_default_tactic(m, p));

