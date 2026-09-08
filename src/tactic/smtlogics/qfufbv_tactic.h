/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfufbv_tactic.h

Abstract:

    Tactic for QF_UFBV

Author:

    Leonardo (leonardo) 2012-02-27

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qfufbv_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_qfufbv_ackr_tactic(ast_manager & m, params_ref const & p);

Z3_ADD_TACTIC(qfufbv, "qfufbv", "builtin strategy for solving QF_UFBV problems.", mk_qfufbv_tactic(m, p));
Z3_ADD_TACTIC(qfufbv_ackr, "qfufbv_ackr", "A tactic for solving QF_UFBV based on Ackermannization.", mk_qfufbv_ackr_tactic(m, p));

