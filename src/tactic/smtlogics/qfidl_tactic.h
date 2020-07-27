/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfidl_tactic.h

Abstract:

    Tactic for QF_IDL

Author:

    Leonardo (leonardo) 2012-02-21

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfidl_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("qfidl", "builtin strategy for solving QF_IDL problems.", "mk_qfidl_tactic(m, p)")
*/

