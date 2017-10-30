/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_tactic.h

Abstract:

    Tactic for QF_NRA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#ifndef QFNRA_TACTIC_H_
#define QFNRA_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfnra_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qfnra", "builtin strategy for solving QF_NRA problems.", "mk_qfnra_tactic(m, p)")
*/

#endif
