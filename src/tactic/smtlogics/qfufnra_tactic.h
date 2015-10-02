/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfufnra_tactic.h

Abstract:

    Tactic for QF_UFNRA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#ifndef QFUFNRA_TACTIC_H_
#define QFUFNRA_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qfufnra_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qfufnra", "builtin strategy for solving QF_UNFRA problems.", "mk_qfufnra_tactic(m, p)")
*/

#endif
