/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfauflia_tactic.h

Abstract:

    Tactic for QF_AUFLIA

Author:

    Leonardo (leonardo) 2012-02-21

Notes:

--*/
#ifndef QFAUFLIA_TACTIC_H_
#define QFAUFLIA_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfauflia_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("qfauflia",  "builtin strategy for solving QF_AUFLIA problems.", "mk_qfauflia_tactic(m, p)")
*/

#endif
