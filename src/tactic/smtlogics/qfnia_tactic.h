/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnia_tactic.h

Abstract:

    Tactic for QF_NIA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qfnia_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(qfnia, "qfnia", "builtin strategy for solving QF_NIA problems.", mk_qfnia_tactic(m, p));

