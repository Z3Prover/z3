/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfaufbv_tactic.h

Abstract:

    Tactic for QF_AUFBV

Author:

    Leonardo (leonardo) 2012-02-23

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(qfaufbv, "qfaufbv", "builtin strategy for solving QF_AUFBV problems.", mk_qfaufbv_tactic(m, p));

