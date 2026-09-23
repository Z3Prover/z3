/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nra_tactic.h

Abstract:

    Tactic for NRA

Author:

    Leonardo (leonardo) 2012-03-13

Notes:

--*/
#pragma once
#include "tactic/tactic.h"

tactic * mk_nra_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(nra, "nra", "builtin strategy for solving NRA problems.", mk_nra_tactic(m, p));

