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
#ifndef _QFUFBV_TACTIC_
#define _QFUFBV_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qfufbv_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
