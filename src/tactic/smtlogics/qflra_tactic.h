/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qflra_tactic.h

Abstract:

    Tactic for QF_LRA

Author:

    Leonardo (leonardo) 2012-02-26

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qflra_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(qflra, "qflra", "builtin strategy for solving QF_LRA problems.", mk_qflra_tactic(m, p));

