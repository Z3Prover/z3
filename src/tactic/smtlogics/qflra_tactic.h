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
#ifndef _QFLRA_TACTIC_
#define _QFLRA_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qflra_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qflra", "builtin strategy for solving QF_LRA problems.", "mk_qflra_tactic(m, p)")
*/

#endif
